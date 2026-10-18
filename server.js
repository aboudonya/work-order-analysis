// Local Work Orders viewer for Oracle Fusion REST API
// Run:  node server.js   (Node 18+ required, no npm packages needed)
// Open: http://localhost:3000

const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const HOST = (process.env.FUSION_HOST || 'https://fa-exkc-saasfaprod1.fa.ocs.oraclecloud.com').replace(/\/+$/, '');
const VERSION = process.env.FUSION_VERSION || '11.13.18.05';
const RESOURCE = `/fscmRestApi/resources/${VERSION}/maintenanceWorkOrders`;
// Try different component endpoint variations
const COMPONENT_RESOURCE = `/fscmRestApi/resources/${VERSION}/maintenanceWorkOrderComponents`;
const REQUIREMENT_RESOURCE = `/fscmRestApi/resources/${VERSION}/maintenanceWorkOrderRequirements`;
const MATERIAL_ISSUES_RESOURCE = `/fscmRestApi/resources/${VERSION}/materialIssuesAndReversals`;
const INVENTORY_TRANSACTIONS_RESOURCE = `/fscmRestApi/resources/${VERSION}/inventoryCompletedTransactions`;
const PAGE_SIZE = 500;                  // Max limit allowed by Fusion
const CACHE_TTL = 30 * 60 * 1000;       // Page cache: 30 minutes
const SESSION_TTL = 8 * 60 * 60 * 1000; // Session: 8 hours from last activity
const CACHE_MAX = 500;                  // Max cached pages per session

const FIELD_RE = /^[A-Za-z0-9_,]{1,2000}$/;
const ORDER_RE = /^[A-Za-z0-9_]+(:(asc|desc))?$/i;

const sessions = new Map(); // sid -> { user, auth, last, cache: Map }
const loginFails = new Map(); // ip -> { count, lockedUntil }
const LOGIN_MAX_FAILS = 5, LOGIN_LOCK_MS = 60 * 1000;
function loginLocked(ip) {
  const f = loginFails.get(ip);
  return f && f.lockedUntil && Date.now() < f.lockedUntil;
}
function recordLoginFail(ip) {
  const f = loginFails.get(ip) || { count: 0, lockedUntil: 0 };
  f.count++;
  if (f.count >= LOGIN_MAX_FAILS) { f.lockedUntil = Date.now() + LOGIN_LOCK_MS; f.count = 0; }
  loginFails.set(ip, f);
}
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

setInterval(() => {
  const now = Date.now();
  for (const [sid, s] of sessions) if (now - s.last > SESSION_TTL) sessions.delete(sid);
}, 10 * 60 * 1000).unref();

const SEC_HEADERS = { 'X-Content-Type-Options': 'nosniff', 'X-Frame-Options': 'DENY', 'Referrer-Policy': 'no-referrer' };
function send(res, status, obj, headers = {}) {
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', ...SEC_HEADERS, ...headers });
  res.end(JSON.stringify(obj));
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let data = '';
    req.on('data', (c) => { data += c; if (data.length > 1e6) { req.destroy(); reject(new Error('too large')); } });
    req.on('end', () => resolve(data));
    req.on('error', reject);
  });
}

function sidFrom(req) {
  const m = /(?:^|;\s*)sid=([a-f0-9]+)/.exec(req.headers.cookie || '');
  return m ? m[1] : null;
}

function getSession(req) {
  const sid = sidFrom(req);
  const s = sid && sessions.get(sid);
  if (!s) return null;
  if (Date.now() - s.last > SESSION_TTL) { sessions.delete(sid); return null; }
  s.last = Date.now();
  return s;
}

// Single Fusion request with automatic retry on 429 / 502 / 503 / 504 or network errors
async function callFusion(session, params, resource = RESOURCE) {
  const url = HOST + resource + '?' + new URLSearchParams(params).toString();
  let lastErr;
  for (let attempt = 0; attempt < 3; attempt++) {
    const ctrl = new AbortController();
    const timer = setTimeout(() => ctrl.abort(), 90000);
    try {
      const r = await fetch(url, {
        headers: { Authorization: session.auth, Accept: 'application/json' },
        signal: ctrl.signal,
      });
      const text = await r.text();
      if ([429, 502, 503, 504].includes(r.status) && attempt < 2) { await sleep(700 * (attempt + 1)); continue; }
      let json = null;
      try { json = JSON.parse(text); } catch (_) { /* not json */ }
      return { status: r.status, json, text };
    } catch (e) {
      lastErr = e;
      if (e.name === 'AbortError' || attempt === 2) throw e;
      await sleep(500 * (attempt + 1));
    } finally {
      clearTimeout(timer);
    }
  }
  throw lastErr;
}

const strip = (it) => { const { links, ...rest } = it; return rest; };

// Run async tasks over an array with limited concurrency
async function pool(arr, size, fn) {
  let idx = 0;
  const worker = async () => { while (idx < arr.length) { const i = idx++; await fn(arr[i], i); } };
  await Promise.all(Array.from({ length: Math.min(size, arr.length) }, worker));
}

function cacheGet(session, key, refresh) {
  const hit = session.cache.get(key);
  return !refresh && hit && Date.now() - hit.ts < CACHE_TTL ? hit.data : null;
}
function cacheSet(session, key, data) {
  const now = Date.now();
  session.cache.set(key, { ts: now, data });
  for (const [k, v] of session.cache) if (now - v.ts > CACHE_TTL) session.cache.delete(k);
  while (session.cache.size > CACHE_MAX) session.cache.delete(session.cache.keys().next().value);
}

function fusionError(res, r) {
  if (r.status === 401 || r.status === 403) return send(res, 401, { error: 'Session expired or insufficient permissions' });
  return send(res, r.status === 400 ? 400 : 502, { error: `Fusion returned error ${r.status}`, detail: (r.text || '').slice(0, 300) });
}

// Bounded, read-only traversal of child resources advertised by this work order.
// No guessed resource paths, no root-collection substitution, no unrelated-order joins.
async function workOrderBundle(session, woId) {
  const root = RESOURCE + '/' + woId;
  const host = new URL(HOST);
  const budget = { requests: 0, rows: 0, collections: 0, started: Date.now() };
  const limits = { requests: 120, rows: 20000, collections: 100, depth: 3, ms: 120000 };
  const sections = new Map(), seen = new Set(), queue = [], warnings = [];
  let complete = true;
  function warn(message) { complete = false; if (!warnings.includes(message)) warnings.push(message); }
  function resourceURL(href) {
    try {
      const u = new URL(href, HOST + root + '/');
      if (u.origin !== host.origin || u.username || u.password || u.hash || !u.pathname.startsWith(root + '/child/')) return null;
      // Reject encoded separators, traversal and control characters, including double encoding.
      if (/%(?:2f|5c|2e|25|00|0a|0d)/i.test(u.pathname) || /[\\\x00-\x20]/.test(u.pathname)) return null;
      return u;
    } catch { return null; }
  }
  function exhausted() {
    return budget.requests >= limits.requests || budget.rows >= limits.rows || Date.now() - budget.started > limits.ms;
  }
  async function read(resource, params) {
    if (exhausted()) throw new Error('Related-data request, row or time safety limit reached');
    budget.requests++;
    const r = await callFusion(session, params, resource);
    if (r.status !== 200 || !r.json) {
      const e = new Error(r.status === 403 ? 'Permission denied by Fusion (403)' : r.status === 401 ? 'Fusion authentication expired (401)' : r.status === 404 ? 'Advertised resource not found (404)' : 'Fusion response ' + r.status + (r.json ? '' : ' (not JSON)'));
      e.status = r.status; throw e;
    }
    return r.json;
  }
  function contextFor(row, inherited) {
    const context = { ...inherited };
    for (const key of ['WoOperationId','WorkOrderOperationId','OperationSequenceNumber','OperationName','WorkCenterCode','ResourceCode']) {
      if (row[key] !== undefined && row[key] !== null) context['Parent' + key] = row[key];
    }
    return context;
  }
  function discover(row, depth, context) {
    for (const link of Array.isArray(row.links) ? row.links : []) {
      if (!['child','collection'].includes(link.rel)) continue;
      const u = resourceURL(link.href);
      if (!u) { warn('A child link outside the permitted work-order scope was ignored.'); continue; }
      const identity = u.pathname + '?' + [...u.searchParams].filter(([k]) => !['offset','limit','onlyData'].includes(k)).sort().map(([k,v]) => k + '=' + v).join('&');
      if (seen.has(identity)) continue;
      seen.add(identity);
      const chain = u.pathname.slice(root.length).split('/child/').slice(1).map(part => part.split('/')[0]);
      const key = chain.join('/');
      const name = String(link.name || chain[chain.length - 1] || 'Related data');
      let section = sections.get(key);
      if (!section) {
        section = { key, title: name.replace(/([a-z0-9])([A-Z])/g, '$1 $2'), items: [], status: 'ok', source: root + '/child/' + chain[0], sources: [], errors: [] };
        sections.set(key, section);
      }
      if (depth > limits.depth || budget.collections >= limits.collections) {
        section.status = 'partial'; section.errors.push('Discovery depth or collection safety limit reached');
        warn('Some child datasets exceed discovery limits; the bundle is incomplete.'); continue;
      }
      budget.collections++;
      section.sources.push(u.pathname);
      queue.push({ u, section, depth, context });
    }
  }
  const header = await read(root, { onlyData: 'false' });
  const item = Array.isArray(header.items) ? header.items[0] : header;
  if (!item || typeof item !== 'object') throw new Error('Fusion did not return a work-order object');
  if (item.WorkOrderId !== undefined && String(item.WorkOrderId) !== woId) throw new Error('Fusion returned a different work order');
  discover(item, 1, {});
  if (!queue.length && !sections.size) warnings.push('Fusion advertised no child collections for this order. Additional datasets may require different permissions or APIs.');
  while (queue.length) {
    const job = queue.shift(), { section, depth, context } = job;
    let offset = 0, hadRows = false, pageFingerprints = new Set();
    try {
      while (true) {
        const params = Object.fromEntries(job.u.searchParams);
        delete params.fields; delete params.expand;
        Object.assign(params, { limit: '200', offset: String(offset), onlyData: 'false' });
        const data = await read(job.u.pathname, params);
        if (!Array.isArray(data.items)) throw new Error('Advertised collection response has no items array');
        const rows = data.items;
        if (data.hasMore && !rows.length) throw new Error('Fusion reported more rows but returned an empty page');
        // Guard against endpoints that ignore offset (rather than silently duplicating rows).
        const fingerprint = JSON.stringify(rows);
        if (rows.length && pageFingerprints.has(fingerprint)) throw new Error('Pagination repeated a page; remaining rows are unknown');
        pageFingerprints.add(fingerprint);
        for (const row of rows) {
          if (budget.rows >= limits.rows) throw new Error('Related-data row safety limit reached');
          if (!row || typeof row !== 'object') throw new Error('Invalid collection record');
          section.items.push({ ...context, ...strip(row) }); budget.rows++; hadRows = true;
          discover(row, depth + 1, contextFor(row, context));
        }
        if (!data.hasMore) break;
        offset += rows.length; // Respect actual server page size, not requested limit.
      }
    } catch (e) {
      section.status = hadRows || section.items.length || section.status === 'partial' ? 'partial' : e.status === 403 ? 'forbidden' : e.status === 404 ? 'unavailable' : 'error';
      section.errors.push(e.message);
      warn(section.title + ': ' + e.message);
      if (e.status === 401) warn('Authentication expired while loading related data. Sign in again.');
    }
    if (exhausted() && queue.length) {
      for (const pending of queue) {
        pending.section.status = 'partial';
        pending.section.errors.push('Not loaded: related-data safety budget reached');
      }
      warn('Discovery stopped at the request, row or time safety limit. Some datasets have not been loaded.');
      break;
    }
  }
  for (const section of sections.values()) {
    if (section.status === 'ok' && !section.items.length) section.status = 'empty';
    if (section.errors.length) section.error = [...new Set(section.errors)].join('; ');
    delete section.errors;
  }
  return { item: strip(item), sections: [...sections.values()], warnings, complete, limits, fetchedAt: new Date().toISOString() };
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://localhost');
  try {
    if (req.method === 'GET' && url.pathname === '/echarts.min.js') {
      try {
        const js = fs.readFileSync(path.join(__dirname, 'echarts.min.js'));
        res.writeHead(200, { 'Content-Type': 'application/javascript; charset=utf-8', 'Cache-Control': 'public, max-age=86400' });
        return res.end(js);
      } catch { res.writeHead(404); return res.end('echarts.min.js not found'); }
    }
    if (req.method === 'GET' && (url.pathname === '/' || url.pathname === '/index.html')) {
      const html = fs.readFileSync(path.join(__dirname, 'index.html'));
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store', ...SEC_HEADERS,
        'Content-Security-Policy': "default-src 'self'; style-src 'unsafe-inline' 'self'; script-src 'unsafe-inline' 'self' https://cdn.jsdelivr.net; img-src 'self' data:; connect-src 'self'" });
      return res.end(html);
    }

    if (req.method === 'GET' && url.pathname === '/api/info') {
      const s = getSession(req);
      return send(res, 200, { host: HOST, version: VERSION, loggedIn: !!s, user: s ? s.user : null });
    }

    if (req.method === 'POST' && url.pathname === '/api/login') {
      const ip = req.socket.remoteAddress || 'unknown';
      if (loginLocked(ip)) return send(res, 429, { error: 'Too many failed attempts — wait 60 seconds and try again' });
      const { username, password } = JSON.parse((await readBody(req)) || '{}');
      if (!username || !password) return send(res, 400, { error: 'Enter your username and password' });
      const session = {
        user: username,
        auth: 'Basic ' + Buffer.from(`${username}:${password}`, 'utf8').toString('base64'),
        last: Date.now(),
        cache: new Map(),
      };
      const r = await callFusion(session, { limit: '1', onlyData: 'true' });
      if (r.status === 401 || r.status === 403) { recordLoginFail(ip); return send(res, 401, { error: 'Invalid username or password (or account lacks maintenance work order permissions)' }); }
      if (r.status !== 200) return send(res, 502, { error: `Fusion returned error ${r.status}`, detail: (r.text || '').slice(0, 300) });
      loginFails.delete(ip);
      const sid = crypto.randomBytes(24).toString('hex');
      sessions.set(sid, session);
      return send(res, 200, { ok: true, user: username }, { 'Set-Cookie': `sid=${sid}; HttpOnly; SameSite=Strict; Path=/; Max-Age=${Math.floor(SESSION_TTL / 1000)}` });
    }

    if (req.method === 'POST' && url.pathname === '/api/logout') {
      const sid = sidFrom(req);
      if (sid) sessions.delete(sid);
      return send(res, 200, { ok: true }, { 'Set-Cookie': 'sid=; HttpOnly; SameSite=Strict; Path=/; Max-Age=0' });
    }

    // Header plus related datasets discovered from this work order's own links.
    if (req.method === 'GET' && url.pathname === '/api/workorderbundle') {
      const session = getSession(req);
      if (!session) return send(res, 401, { error: 'Please log in first' });
      const woId = url.searchParams.get('woId') || '';
      if (!/^\d{1,20}$/.test(woId)) return send(res, 400, { error: 'A numeric Work Order ID is required' });
      const key = 'bundle|' + woId;
      const cached = cacheGet(session, key, url.searchParams.get('refresh') === '1');
      if (cached) return send(res, 200, { ...cached, cached: true });
      try {
        const data = await workOrderBundle(session, woId);
        if (data.complete) cacheSet(session, key, data);
        return send(res, 200, data);
      } catch (e) {
        return send(res, [401,403,404].includes(e.status) ? e.status : 502, { error: e.message });
      }
    }

    // Available columns + total count (lightweight: 1 row only)
    if (req.method === 'GET' && url.pathname === '/api/meta') {
      const session = getSession(req);
      if (!session) return send(res, 401, { error: 'Please log in first' });
      const q = (url.searchParams.get('q') || '').slice(0, 500);
      const refresh = url.searchParams.get('refresh') === '1';
      const key = 'meta|' + q;
      const cached = cacheGet(session, key, refresh);
      if (cached) return send(res, 200, { ...cached, cached: true });

      const params = { limit: '1', onlyData: 'true', totalResults: 'true' };
      if (q) params.q = q;
      const r = await callFusion(session, params);
      if (r.status !== 200 || !r.json) return fusionError(res, r);
      const first = (r.json.items || [])[0];
      const data = {
        keys: first ? Object.keys(strip(first)) : [],
        total: typeof r.json.totalResults === 'number' ? r.json.totalResults : null,
      };
      cacheSet(session, key, data);
      return send(res, 200, data);
    }

    // Page of work orders (enriched with operations and materials in main table columns)
    if (req.method === 'GET' && url.pathname === '/api/workorders') {
      const session = getSession(req);
      if (!session) return send(res, 401, { error: 'Please log in first' });

      const sp = url.searchParams;
      const params = {
        limit: String(Math.min(Math.max(1, parseInt(sp.get('limit') || PAGE_SIZE, 10) || PAGE_SIZE), PAGE_SIZE)),
        offset: String(Math.max(0, parseInt(sp.get('offset') || '0', 10) || 0)),
        onlyData: 'true',
      };
      const fields = sp.get('fields'); if (fields && FIELD_RE.test(fields)) params.fields = fields;
      const orderBy = sp.get('orderBy'); if (orderBy && ORDER_RE.test(orderBy)) params.orderBy = orderBy;
      const q = sp.get('q'); if (q) params.q = q.slice(0, 500);

      const key = 'page|' + (sp.get('enrich') === '1' ? 'e|' : '') + JSON.stringify(params);
      const cached = cacheGet(session, key, sp.get('refresh') === '1');
      if (cached) return send(res, 200, { ...cached, cached: true });

      const r = await callFusion(session, params);
      if (r.status !== 200 || !r.json) return fusionError(res, r);
      let items = (r.json.items || []).map(strip);

      // Enrich each work order with operation & material columns (parallel, limited concurrency)
      // Details per work order are slow (many extra requests); only fetch when ?enrich=1
      if (sp.get('enrich') === '1') await pool(items, 5, async (wo) => {
        const woId = wo.WorkOrderId;
        if (!woId) return;
        try {
          // Try fetching operations via child endpoints or direct component/requirement fallbacks
          let operations = [];
          const opRes = await callFusion(session, { limit: '20', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/WorkOrderOperation');
          if (opRes.status === 200 && opRes.json && opRes.json.items) {
            operations = opRes.json.items;
          } else {
            const opRes2 = await callFusion(session, { limit: '20', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/maintenanceWorkOrderOperations');
            if (opRes2.status === 200 && opRes2.json && opRes2.json.items) {
              operations = opRes2.json.items;
            }
          }

          let opIdx = 1;
          if (operations.length > 0) {
            for (const op of operations) {
              const woOpId = op.WoOperationId;
              const opName = op.OperationName || op.StandardOperationName || ('Op ' + opIdx);

              wo[`op${opIdx}_name`] = opName;
              wo[`op${opIdx}_seq`] = op.OperationSequenceNumber || '';

              if (woOpId != null) {
                // Try fetching operation material via child resource path
                const matRes = await callFusion(session, { limit: '20', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/WorkOrderOperation/' + woOpId + '/child/WorkOrderOperationMaterial');
                let itemsList = (matRes.status === 200 && matRes.json && matRes.json.items) ? matRes.json.items : [];

                // If empty, try fallback child resource name
                if (itemsList.length === 0) {
                  const matRes2 = await callFusion(session, { limit: '20', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/WorkOrderOperation/' + woOpId + '/child/workOrderOperationMaterials');
                  if (matRes2.status === 200 && matRes2.json && matRes2.json.items) {
                    itemsList = matRes2.json.items;
                  }
                }

                // If still empty, query global requirements or components filtered by OperationSequenceNumber or WoOperationId
                if (itemsList.length === 0) {
                  const reqRes = await callFusion(session, { q: `WorkOrderId=${woId}`, limit: '50', onlyData: 'true' }, REQUIREMENT_RESOURCE);
                  if (reqRes.status === 200 && reqRes.json && reqRes.json.items) {
                    itemsList = reqRes.json.items.filter(m => String(m.OperationSequenceNumber) === String(op.OperationSequenceNumber));
                  }
                }

                if (itemsList.length > 0) {
                  wo[`op${opIdx}_item`] = itemsList.map(m => m.ItemNumber || m.InventoryItemNumber).filter(Boolean).join(', ');
                  wo[`op${opIdx}_desc`] = itemsList.map(m => m.ItemDescription).filter(Boolean).join('; ');
                  wo[`op${opIdx}_requiredqty`] = itemsList.reduce((sum, m) => sum + (Number(m.RequiredQuantity ?? m.Quantity) || 0), 0);
                  wo[`op${opIdx}_issuedqty`] = itemsList.reduce((sum, m) => sum + (Number(m.IssuedQuantity) || 0), 0);
                }
              }
              opIdx++;
              if (opIdx > 5) break;
            }
          } else {
            // If no operations child collection, fallback to querying work order components directly
            const compRes = await callFusion(session, { limit: '10', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/maintenanceWorkOrderComponents');
            if (compRes.status === 200 && compRes.json && compRes.json.items) {
              let idx = 1;
              for (const comp of compRes.json.items) {
                wo[`op${idx}_name`] = comp.OperationName || comp.StandardOperation || ('Op ' + idx);
                wo[`op${idx}_item`] = comp.ItemNumber || '';
                wo[`op${idx}_desc`] = comp.ItemDescription || '';
                wo[`op${idx}_requiredqty`] = comp.RequiredQuantity ?? comp.Quantity ?? '';
                wo[`op${idx}_issuedqty`] = comp.IssuedQuantity ?? '';
                idx++;
                if (idx > 5) break;
              }
            }
          }
        } catch (e) { console.warn(`Enrichment failed for WO ${wo.WorkOrderId}:`, e.message); }

        // Totals across all operations -> main table columns
        let reqT = 0, issT = 0, any = false;
        for (let i = 1; i <= 5; i++) {
          const rq = wo[`op${i}_requiredqty`], is = wo[`op${i}_issuedqty`];
          if (rq !== undefined && rq !== '') { reqT += Number(rq) || 0; any = true; }
          if (is !== undefined && is !== '') { issT += Number(is) || 0; any = true; }
        }
        if (any) { wo.requiredqty = reqT; wo.issuedqty = issT; }
        
        // Ensure WorkDefinition is set
        if (!wo.WorkDefinition) {
          wo.WorkDefinition = wo.WorkDefinitionName || wo.WorkDefinitionCode || wo.MntWorkDefinitionName || wo.MntWorkDefinitionCode || '';
        }
        if (!wo.WorkDefinition && operations.length > 0) {
          const def = operations.map(o => o.WorkDefinitionName || o.WorkDefinition || o.WorkDefinitionCode || o.MntWorkDefinitionName || o.MntWorkDefinitionCode).filter(Boolean)[0];
          if (def) wo.WorkDefinition = def;
        }
      });

      const data = { items, hasMore: !!r.json.hasMore, count: items.length };
      cacheSet(session, key, data);
      return send(res, 200, data);
    }

    // Full details for a single work order (all columns)
    if (req.method === 'GET' && url.pathname === '/api/workorder') {
      const session = getSession(req);
      if (!session) return send(res, 401, { error: 'Please log in first' });
      const id = url.searchParams.get('id') || '';
      if (!/^\d{1,20}$/.test(id)) return send(res, 400, { error: 'Invalid ID' });
      const key = 'one|' + id;
      const cached = cacheGet(session, key, false);
      if (cached) return send(res, 200, cached);
      const r = await callFusion(session, { q: `WorkOrderId=${id}`, limit: '1', onlyData: 'true' });
      if (r.status !== 200 || !r.json) return fusionError(res, r);
      const item = (r.json.items || [])[0];
      if (!item) return send(res, 404, { error: 'Work order not found' });
      const data = { item: strip(item) };
      cacheSet(session, key, data);
      return send(res, 200, data);
    }

    // Work Order Components (digs through WorkOrderOperation -> WorkOrderOperationMaterial)
    if (req.method === 'GET' && url.pathname === '/api/workordercomponents') {
      const session = getSession(req);
      if (!session) return send(res, 401, { error: 'Please log in first' });
      const woId = url.searchParams.get('woId') || '';
      if (!/^\d{1,20}$/.test(woId)) return send(res, 400, { error: 'Invalid Work Order ID' });
      const key = 'components_deep|' + woId;
      const cached = cacheGet(session, key, url.searchParams.get('refresh') === '1');
      if (cached) return send(res, 200, { ...cached, cached: true });

      let combinedItems = [];

      try {
        // Step 1: Fetch operations for this work order (/maintenanceWorkOrders/{id}/child/WorkOrderOperation)
        const opRes = await callFusion(session, { limit: '100', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/WorkOrderOperation');
        let operations = [];
        if (opRes.status === 200 && opRes.json && opRes.json.items) {
          operations = opRes.json.items;
        } else {
          // Try fallback operation child resource name
          const opRes2 = await callFusion(session, { limit: '100', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/maintenanceWorkOrderOperations');
          if (opRes2.status === 200 && opRes2.json && opRes2.json.items) {
            operations = opRes2.json.items;
          }
        }

        // For each operation, fetch operation materials using WoOperationId
        for (const op of operations) {
          const woOpId = op.WoOperationId;
          const opSeq = op.OperationSequenceNumber || op.OperationSeqNum || op.OperationSequence || op.sequenceNumber;
          const opName = op.OperationName || op.StandardOperationName || op.OperationCode || '';
          const workDef = op.WorkDefinitionName || op.WorkDefinition || '';
          const stdOp = op.StandardOperationCode || op.StandardOperation || op.StandardOperationName || '';

          if (woOpId != null) {
            const matRes = await callFusion(session, { limit: '100', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/WorkOrderOperation/' + woOpId + '/child/WorkOrderOperationMaterial');
            if (matRes.status === 200 && matRes.json && matRes.json.items) {
              for (const mat of matRes.json.items) {
                combinedItems.push(strip({
                  ...mat,
                  WorkDefinition: workDef || mat.WorkDefinition || '',
                  StandardOperation: stdOp || mat.StandardOperation || '',
                  OperationSequenceNumber: opSeq,
                  OperationName: opName || mat.OperationName || '',
                }));
              }
            }
          }
        }

        // Fallback or direct check: try maintenanceWorkOrderComponents and maintenanceWorkOrderRequirements child resources directly
        if (combinedItems.length === 0) {
          for (const subRes of ['maintenanceWorkOrderComponents', 'maintenanceWorkOrderRequirements', 'maintenanceWorkOrderMaterials']) {
            try {
              const r = await callFusion(session, { limit: '1000', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/' + subRes);
              if (r.status === 200 && r.json && r.json.items && r.json.items.length > 0) {
                combinedItems = r.json.items.map(strip);
                break;
              }
            } catch (e) { console.warn(`Child resource ${subRes} failed for WO ${woId}:`, e.message); }
          }
        }

        // If still empty, try global root resources filtered by WorkOrderId
        if (combinedItems.length === 0) {
          for (const rootRes of [COMPONENT_RESOURCE, REQUIREMENT_RESOURCE, MATERIAL_ISSUES_RESOURCE, INVENTORY_TRANSACTIONS_RESOURCE]) {
            try {
              const r = await callFusion(session, { q: `WorkOrderId=${woId}`, limit: '1000', onlyData: 'true' }, rootRes);
              if (r.status === 200 && r.json && r.json.items && r.json.items.length > 0) {
                combinedItems = r.json.items.map(strip);
                break;
              }
            } catch (e) { console.warn(`Root resource ${rootRes} failed for WO ${woId}:`, e.message); }
          }
        }
      } catch (err) {
        console.warn(`Component traversal failed for WO ${woId}:`, err.message);
        // If child traversal encounters any issue, fallback to standard components
        try {
          const r = await callFusion(session, { limit: '1000', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/maintenanceWorkOrderComponents');
          if (r.status === 200 && r.json && r.json.items) {
            combinedItems = (r.json.items || []).map(strip);
          }
        } catch (e) { console.warn(`Component fallback failed for WO ${woId}:`, e.message); }
      }

      const data = { items: combinedItems, count: combinedItems.length };
      cacheSet(session, key, data);
      return send(res, 200, data);
    }

    // Work Order Requirements
    if (req.method === 'GET' && url.pathname === '/api/workorderrequirements') {
      const session = getSession(req);
      if (!session) return send(res, 401, { error: 'Please log in first' });
      const woId = url.searchParams.get('woId') || '';
      if (!/^\d{1,20}$/.test(woId)) return send(res, 400, { error: 'Invalid Work Order ID' });
      const key = 'requirements|' + woId;
      const cached = cacheGet(session, key, url.searchParams.get('refresh') === '1');
      if (cached) return send(res, 200, { ...cached, cached: true });

      const r = await callFusion(session, { q: `WorkOrderId=${woId}`, limit: '1000', onlyData: 'true' }, REQUIREMENT_RESOURCE);
      if (r.status === 200 && r.json && r.json.items) {
        const items = (r.json.items || []).map(strip);
        const data = { items, count: items.length };
        cacheSet(session, key, data);
        return send(res, 200, data);
      }

      // Fallback
      const r2 = await callFusion(session, { q: `WorkOrderId=${woId}`, limit: '1000', onlyData: 'true' }, RESOURCE + '/' + woId + '/child/maintenanceWorkOrderRequirements');
      if (r2.status !== 200 || !r2.json) return fusionError(res, r2);
      const items = (r2.json.items || []).map(strip);
      const data = { items, count: items.length };
      cacheSet(session, key, data);
      return send(res, 200, data);
    }

    // Material Issues (issued items) - can filter by WorkOrderId
    if (req.method === 'GET' && url.pathname === '/api/materialissues') {
      const session = getSession(req);
      if (!session) return send(res, 401, { error: 'Please log in first' });
      const woId = url.searchParams.get('woId') || '';
      if (!/^\d{1,20}$/.test(woId)) return send(res, 400, { error: 'A numeric Work Order ID is required' });
      const q = `WorkOrderId=${woId}`;
      const key = 'materialissues|' + woId;
      const cached = cacheGet(session, key, url.searchParams.get('refresh') === '1');
      if (cached) return send(res, 200, { ...cached, cached: true });

      const params = { limit: '1000', onlyData: 'true' };
      if (q) params.q = q;
      const r = await callFusion(session, params, MATERIAL_ISSUES_RESOURCE);
      if (r.status !== 200 || !r.json) return fusionError(res, r);
      const items = (r.json.items || []).map(strip);
      const data = { items, count: items.length };
      cacheSet(session, key, data);
      return send(res, 200, data);
    }

    // Inventory Completed Transactions (all transactions including issues)
    if (req.method === 'GET' && url.pathname === '/api/inventorytransactions') {
      const session = getSession(req);
      if (!session) return send(res, 401, { error: 'Please log in first' });
      const woId = url.searchParams.get('woId') || '';
      if (!/^\d{1,20}$/.test(woId)) return send(res, 400, { error: 'A numeric Work Order ID is required' });
      const q = `WorkOrderId=${woId}`;
      const key = 'inventorytxn|' + woId;
      const cached = cacheGet(session, key, url.searchParams.get('refresh') === '1');
      if (cached) return send(res, 200, { ...cached, cached: true });

      const params = { limit: '1000', onlyData: 'true' };
      if (q) params.q = q;
      const r = await callFusion(session, params, INVENTORY_TRANSACTIONS_RESOURCE);
      if (r.status !== 200 || !r.json) return fusionError(res, r);
      const items = (r.json.items || []).map(strip);
      const data = { items, count: items.length };
      cacheSet(session, key, data);
      return send(res, 200, data);
    }

    send(res, 404, { error: 'not found' });
  } catch (e) {
    const msg = e.name === 'AbortError' ? 'Connection to Fusion timed out' : e.message;
    send(res, 500, { error: msg });
  }
});

// Server listens on localhost only (127.0.0.1)
server.listen(PORT, '127.0.0.1', () => {
  console.log(`App running at: http://localhost:${PORT}`);
  console.log(`Fusion: ${HOST}${RESOURCE}`);
});
