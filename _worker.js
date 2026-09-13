import { connect } from "cloudflare:sockets";

// ============================================
// ENV CONFIG
// ============================================
let userID = "";
let trojanPass = "";
let proxyListURL = "";

// ============================================
// CLEAN PROXY POOL (dead domains removed)
// ============================================
const PROXY_POOL = [
    "31.58.9.4:6077",
    "194.39.32.164:6461"
];

// ============================================
// DoH PROVIDERS
// ============================================
const DOH_URLS = [
    "https://cloudflare-dns.com/dns-query",
    "https://1.1.1.1/dns-query",
    "https://dns.google/dns-query",
    "https://8.8.8.8/dns-query",
    "https://dns.quad9.net/dns-query",
    "https://9.9.9.9/dns-query",
    "https://dns.alidns.com/dns-query",
    "https://doh.pub/dns-query",
    "https://doh.opendns.com/dns-query",
];

// ============================================
// STATE
// ============================================
let healthyProxies = [];
let proxyIdx = 0;
let lastHealthCheck = 0;
const HEALTH_INTERVAL = 60000;
const HEALTH_TIMEOUT = 3000;

// ============================================
// UTILITIES
// ============================================
function isValidUUID(s) {
    return /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i.test(s);
}

function isIP(s) {
    return /^\d+\.\d+\.\d+\.\d+$/.test(s) || /^\[/.test(s);
}

function safeClose(ws) {
    try { if (ws.readyState === 1 || ws.readyState === 2) ws.close(); } catch {}
}

function base64ToBuf(b64) {
    if (!b64) return { data: null, err: null };
    try {
        b64 = b64.replace(/-/g, "+").replace(/_/g, "/");
        const dec = atob(b64);
        return { data: Uint8Array.from(dec, c => c.charCodeAt(0)).buffer, err: null };
    } catch (e) { return { data: null, err: e }; }
}

// ============================================
// SHA224 (Trojan)
// ============================================
function sha224(str) {
    function rot(n, b) { return ((n >>> b) | (n << (32 - b))) >>> 0; }
    const K = [0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
    let s = unescape(encodeURIComponent(str));
    const l = s.length * 8; s += String.fromCharCode(0x80);
    while ((s.length * 8) % 512 !== 448) s += String.fromCharCode(0);
    const h = [0xc1059ed8,0x367cd507,0x3070dd17,0xf70e5939,0xffc00b31,0x68581511,0x64f98fa7,0xbefa4fa4];
    const hi = Math.floor(l / 0x100000000), lo = l & 0xFFFFFFFF;
    s += String.fromCharCode((hi>>>24)&0xFF,(hi>>>16)&0xFF,(hi>>>8)&0xFF,hi&0xFF,(lo>>>24)&0xFF,(lo>>>16)&0xFF,(lo>>>8)&0xFF,lo&0xFF);
    const w = [];
    for (let i = 0; i < s.length; i += 4) w.push((s.charCodeAt(i)<<24)|(s.charCodeAt(i+1)<<16)|(s.charCodeAt(i+2)<<8)|s.charCodeAt(i+3));
    for (let i = 0; i < w.length; i += 16) {
        const x = new Array(64).fill(0);
        for (let j = 0; j < 16; j++) x[j] = w[i+j];
        for (let j = 16; j < 64; j++) {
            const s0 = rot(x[j-15],7)^rot(x[j-15],18)^(x[j-15]>>>3);
            const s1 = rot(x[j-2],17)^rot(x[j-2],19)^(x[j-2]>>>10);
            x[j] = (x[j-16]+s0+x[j-7]+s1)>>>0;
        }
        let [a,b,c,d,e,f,g,h0] = h;
        for (let j = 0; j < 64; j++) {
            const S1 = rot(e,6)^rot(e,11)^rot(e,25), ch = (e&f)^(~e&g), t1 = (h0+S1+ch+K[j]+x[j])>>>0;
            const S0 = rot(a,2)^rot(a,13)^rot(a,22), maj = (a&b)^(a&c)^(b&c), t2 = (S0+maj)>>>0;
            h0 = g; g = f; f = e; e = (d+t1)>>>0; d = c; c = b; b = a; a = (t1+t2)>>>0;
        }
        [h[0],h[1],h[2],h[3],h[4],h[5],h[6],h[7]] = [
            (h[0]+a)>>>0,(h[1]+b)>>>0,(h[2]+c)>>>0,(h[3]+d)>>>0,
            (h[4]+e)>>>0,(h[5]+f)>>>0,(h[6]+g)>>>0,(h[7]+h0)>>>0
        ];
    }
    let hex = '';
    for (let i = 0; i < 7; i++) for (let j = 24; j >= 0; j -= 8) hex += ((h[i]>>>j)&0xFF).toString(16).padStart(2,'0');
    return hex;
}

function hashTrojan(pw) { return sha224(pw); }

// ============================================
// DoH PROXY RESOLUTION (cmliu logic)
// ============================================
async function resolveHost(hostname) {
    if (isIP(hostname)) return [[hostname, 443]];
    
    // Build DNS query for A record
    const enc = new TextEncoder();
    const encodeName = (n) => {
        const parts = n.endsWith('.') ? n.slice(0,-1).split('.') : n.split('.');
        const bufs = [];
        for (const label of parts) { const e = enc.encode(label); bufs.push(new Uint8Array([e.length]), e); }
        bufs.push(new Uint8Array([0]));
        const tot = bufs.reduce((s,b) => s+b.length, 0);
        const r = new Uint8Array(tot); let off = 0;
        for (const b of bufs) { r.set(b, off); off += b.length; }
        return r;
    };
    const qname = encodeName(hostname);
    const query = new Uint8Array(12 + qname.length + 4);
    const dv = new DataView(query.buffer);
    dv.setUint16(0, crypto.getRandomValues(new Uint16Array(1))[0]);
    dv.setUint16(2, 0x0100);
    dv.setUint16(4, 1);
    query.set(qname, 12);
    dv.setUint16(12 + qname.length, 1);  // A record
    dv.setUint16(12 + qname.length + 2, 1);
    
    for (const url of DOH_URLS) {
        try {
            const resp = await fetch(url, {
                method: 'POST',
                headers: {'Content-Type': 'application/dns-message', 'Accept': 'application/dns-message'},
                body: query,
                signal: AbortSignal.timeout(3000)
            });
            if (!resp.ok) continue;
            const buf = new Uint8Array(await resp.arrayBuffer());
            const ddv = new DataView(buf.buffer);
            const ancount = ddv.getUint16(6);
            
            const parseName = (pos) => {
                let p = pos, jumped = false, endPos = -1, safe = 128;
                while (p < buf.length && safe-- > 0) {
                    const len = buf[p];
                    if (len === 0) { if (!jumped) endPos = p + 1; break; }
                    if ((len & 0xC0) === 0xC0) { if (!jumped) endPos = p + 2; p = ((len & 0x3F) << 8) | buf[p + 1]; jumped = true; continue; }
                    p += len + 1;
                }
                return endPos === -1 ? p + 1 : endPos;
            };
            
            let off = 12;
            const qdcount = ddv.getUint16(4);
            for (let i = 0; i < qdcount; i++) { off = parseName(off); off += 4; }
            
            const ips = [];
            for (let i = 0; i < ancount && off < buf.length; i++) {
                off = parseName(off);
                const rtype = ddv.getUint16(off); off += 2; off += 2; off += 4;
                const rdlen = ddv.getUint16(off); off += 2;
                const rdata = buf.slice(off, off + rdlen); off += rdlen;
                if (rtype === 1 && rdlen === 4) {
                    ips.push(`${rdata[0]}.${rdata[1]}.${rdata[2]}.${rdata[3]}`);
                }
            }
            if (ips.length > 0) return ips.map(ip => [ip, 443]);
        } catch {}
    }
    return [[hostname, 443]];
}

// ============================================
// PROXY MANAGEMENT
// ============================================
async function fetchExternalList(rawUrl) {
    if (!rawUrl || rawUrl.includes("YOUR_USERNAME") || rawUrl.includes("example.com")) return [];
    try {
        const r = await fetch(rawUrl, { cf: { cacheTtl: 300, cacheEverything: true }, signal: AbortSignal.timeout(5000) });
        if (r.ok) {
            const t = await r.text();
            return t.split('\n').map(l => l.trim()).filter(l => l.length > 0 && !l.startsWith('#') && l.includes('.')).map(l => l.split(':')[0]);
        }
    } catch {}
    return [];
}

async function healthCheck(host, port = 443) {
    try {
        const s = connect({ hostname: host, port });
        const w = s.writable.getWriter();
        await w.write(new Uint8Array([0x16, 0x03, 0x01, 0x00, 0x05, 0x01, 0x00, 0x02, 0x00, 0x05]));
        w.releaseLock();
        const r = s.readable.getReader();
        const { value } = await Promise.race([
            r.read(),
            new Promise((_, rej) => setTimeout(() => rej(new Error("timeout")), HEALTH_TIMEOUT))
        ]);
        r.releaseLock();
        return value && value.byteLength > 0;
    } catch { return false; }
}

async function refreshProxies() {
    const now = Date.now();
    if (now - lastHealthCheck < HEALTH_INTERVAL && healthyProxies.length > 0) return;
    let list = [...PROXY_POOL];
    const ext = await fetchExternalList(proxyListURL);
    if (ext.length > 0) list = [...ext, ...list];
    list = [...new Set(list)];
    const healthy = [];
    for (let i = 0; i < list.length; i += 5) {
        const batch = list.slice(i, i + 5);
        const res = await Promise.all(batch.map(async h => await healthCheck(h, 443) ? h : null));
        healthy.push(...res.filter(Boolean));
    }
    healthyProxies = healthy.length > 0 ? healthy : list;
    lastHealthCheck = now;
}

function getProxy() {
    if (healthyProxies.length === 0) return PROXY_POOL[Math.floor(Math.random() * PROXY_POOL.length)];
    const p = healthyProxies[proxyIdx % healthyProxies.length];
    proxyIdx++; return p;
}

// ============================================
// VLESS PARSER
// ============================================
function parseVless(buf, uid) {
    if (buf.byteLength < 24) return { err: 'Invalid VLESS data' };
    const ver = new Uint8Array(buf.slice(0, 1))[0];
    const uuidBuf = new Uint8Array(buf.slice(1, 17));
    let uuidStr; try { uuidStr = stringifyUUID(uuidBuf); } catch { return { err: 'Invalid UUID' }; }
    const uuids = uid.includes(',') ? uid.split(',') : [uid];
    if (!uuids.some(u => uuidStr === u.trim())) return { err: 'Invalid user' };
    const optLen = new Uint8Array(buf.slice(17, 18))[0];
    const cmd = new Uint8Array(buf.slice(18 + optLen, 18 + optLen + 1))[0];
    if (cmd !== 1 && cmd !== 2) return { err: `Command ${cmd} not supported` };
    const isUDP = cmd === 2;
    const portIdx = 18 + optLen + 1;
    const portRemote = new DataView(buf.slice(portIdx, portIdx + 2)).getUint16(0);
    let addrIdx = portIdx + 2;
    const addrType = new Uint8Array(buf.slice(addrIdx, addrIdx + 1))[0];
    let addrLen = 0, addrValIdx = addrIdx + 1, addrVal = '';
    switch (addrType) {
        case 1: addrLen = 4; addrVal = Array.from(new Uint8Array(buf.slice(addrValIdx, addrValIdx + addrLen))).join('.'); break;
        case 2: addrLen = new Uint8Array(buf.slice(addrValIdx, addrValIdx + 1))[0]; addrValIdx++; addrVal = new TextDecoder().decode(buf.slice(addrValIdx, addrValIdx + addrLen)); break;
        case 3: addrLen = 16; const dv = new DataView(buf.slice(addrValIdx, addrValIdx + addrLen)); const ip = []; for (let i = 0; i < 8; i++) ip.push(dv.getUint16(i * 2).toString(16)); addrVal = ip.join(':'); break;
        default: return { err: `Invalid address type ${addrType}` };
    }
    if (!addrVal) return { err: 'Empty address' };
    return { err: null, addrRemote: addrVal, addrType, portRemote, rawIdx: addrValIdx + addrLen, responseHeader: new Uint8Array([ver, 0]), isUDP };
}

// ============================================
// TROJAN PARSER
// ============================================
function parseTrojan(buf, pw) {
    if (buf.byteLength < 58) return { err: 'Trojan data too short' };
    const bytes = new Uint8Array(buf);
    if (bytes[56] !== 0x0d || bytes[57] !== 0x0a) return { err: 'Missing CRLF after hash' };
    const gotHash = new TextDecoder().decode(bytes.slice(0, 56));
    if (gotHash !== hashTrojan(pw)) return { err: 'Invalid password' };
    const cmd = bytes[58];
    if (cmd !== 0x01 && cmd !== 0x03) return { err: `Unsupported command ${cmd}` };
    const addrType = bytes[59];
    let addrVal, addrLen, addrValIdx;
    switch (addrType) {
        case 0x01: addrLen = 4; addrValIdx = 60; addrVal = Array.from(bytes.slice(addrValIdx, addrValIdx + addrLen)).join('.'); break;
        case 0x03: addrLen = bytes[60]; addrValIdx = 61; addrVal = new TextDecoder().decode(bytes.slice(addrValIdx, addrValIdx + addrLen)); break;
        case 0x04: addrLen = 16; addrValIdx = 60; addrVal = Array.from({ length: 8 }, (_, i) => new DataView(buf).getUint16(addrValIdx + i * 2).toString(16)).join(':'); break;
        default: return { err: `Invalid address type ${addrType}` };
    }
    const portIdx = addrValIdx + addrLen;
    const portRemote = new DataView(buf).getUint16(portIdx);
    const crlfIdx = portIdx + 2;
    if (bytes[crlfIdx] !== 0x0d || bytes[crlfIdx + 1] !== 0x0a) return { err: 'Missing final CRLF' };
    return { err: null, addrRemote: addrVal, addrType: addrType === 0x03 ? 2 : addrType, portRemote, rawIdx: crlfIdx + 2, responseHeader: new Uint8Array(0), isUDP: cmd === 0x03 };
}

// ============================================
// UUID STRINGIFY
// ============================================
const b2h = [];
for (let i = 0; i < 256; i++) b2h.push((i + 256).toString(16).slice(1));
function unsafeStr(arr, off = 0) {
    return (b2h[arr[off+0]]+b2h[arr[off+1]]+b2h[arr[off+2]]+b2h[arr[off+3]]+'-'+b2h[arr[off+4]]+b2h[arr[off+5]]+'-'+b2h[arr[off+6]]+b2h[arr[off+7]]+'-'+b2h[arr[off+8]]+b2h[arr[off+9]]+'-'+b2h[arr[off+10]]+b2h[arr[off+11]]+b2h[arr[off+12]]+b2h[arr[off+13]]+b2h[arr[off+14]]+b2h[arr[off+15]]).toLowerCase();
}
function stringifyUUID(arr, off = 0) {
    const s = unsafeStr(arr, off);
    if (!isValidUUID(s)) throw new TypeError('Invalid UUID');
    return s;
}

// ============================================
// WS STREAM
// ============================================
function makeWSStream(ws, earlyData, log) {
    return new ReadableStream({
        start(ctrl) {
            ws.addEventListener('message', e => ctrl.enqueue(e.data));
            ws.addEventListener('close', () => { safeClose(ws); ctrl.close(); });
            ws.addEventListener('error', e => { log('WS error'); ctrl.error(e); });
            const { data, err } = base64ToBuf(earlyData);
            if (err) ctrl.error(err); else if (data) ctrl.enqueue(data);
        },
        cancel(reason) { log(`Stream cancel: ${reason}`); safeClose(ws); }
    });
}

// ============================================
// RELAY: REMOTE -> WS
// ============================================
async function relay(remote, ws, responseHeader, retry, log) {
    let header = responseHeader, hasData = false;
    await remote.readable.pipeTo(new WritableStream({
        async write(chunk) {
            hasData = true;
            if (ws.readyState !== 1) throw new Error('WS not open');
            if (header && header.byteLength > 0) {
                ws.send(await new Blob([header, chunk]).arrayBuffer());
                header = null;
            } else ws.send(chunk);
        },
        close() { log(`Remote closed (hadData=${hasData})`); },
        abort(r) { console.error('Remote abort', r); }
    })).catch(e => { console.error('Relay error', e); safeClose(ws); });
    if (!hasData && retry) { log('Retrying...'); retry(); }
}

// ============================================
// TCP OUTBOUND — RACE DIAL (cmliu logic)
// ============================================
async function handleTCP(remoteSocket, addrRemote, portRemote, rawData, ws, responseHeader, addrType, log) {
    
    // Try to connect to a candidate and write data
    async function tryCandidate(c) {
        const socket = connect({ hostname: c.address, port: c.port });
        const writer = socket.writable.getWriter();
        await writer.write(rawData);
        writer.releaseLock();
        return socket;
    }
    
    // Build candidates: direct + resolved proxies
    const candidates = [{ type: 'direct', address: addrRemote, port: portRemote }];
    
    const proxyHost = getProxy();
    if (proxyHost && proxyHost !== addrRemote) {
        try {
            const resolved = await resolveHost(proxyHost);
            for (const [ip, port] of resolved.slice(0, 2)) {
                if (ip !== addrRemote) candidates.push({ type: 'proxy', address: ip, port });
            }
        } catch (e) { log(`Proxy resolve failed: ${e.message}`); }
    }
    
    // RACE: connect all simultaneously, first success wins (cmliu pattern)
    if (candidates.length > 1) {
        const races = candidates.map((c, i) => 
            tryCandidate(c).then(socket => {
                log(`Race winner #${i} [${c.type}] ${c.address}:${c.port}`);
                return { socket, candidate: c };
            }).catch(err => {
                log(`Race loser #${i} [${c.type}] ${c.address}:${c.port} — ${err.message}`);
                throw err;
            })
        );
        
        try {
            const winner = await Promise.any(races);
            remoteSocket.value = winner.socket;
            relay(winner.socket, ws, responseHeader, null, log);
            return;
        } catch {
            log('All race candidates failed, using sequential fallback...');
        }
    }
    
    // SEQUENTIAL FALLBACK (original logic, FIXED)
    async function connectWrite(a, p) {
        const s = connect({ hostname: a, port: p });
        remoteSocket.value = s;
        log(`Connected to ${a}:${p}`);
        const w = s.writable.getWriter();
        await w.write(rawData);
        w.releaseLock();
        return s;
    }
    
    async function doRetry() {
        const p = getProxy();
        log(`Retry via proxy: ${p}`);
        try {
            const s = await connectWrite(p, portRemote);
            // FIXED: pass responseHeader (was null), pass null for retry (was log)
            relay(s, ws, responseHeader, null, log);
        } catch (err) {
            log(`Retry failed: ${err.message}`);
            const p2 = getProxy();
            if (p2 !== p) {
                try {
                    const s2 = await connectWrite(p2, portRemote);
                    relay(s2, ws, responseHeader, null, log);
                } catch (err2) {
                    log(`Fallback failed: ${err2.message}`);
                    safeClose(ws);
                }
            } else safeClose(ws);
        }
    }
    
    try {
        const s = await connectWrite(addrRemote, portRemote);
        relay(s, ws, responseHeader, doRetry, log);
    } catch (err) {
        log(`Direct failed: ${err.message}`);
        doRetry();
    }
}

// ============================================
// UDP / DoH HANDLER
// ============================================
async function handleUDP(ws, responseHeader, log) {
    let headerSent = false;
    const ts = new TransformStream({
        transform(chunk, ctrl) {
            for (let i = 0; i < chunk.byteLength; ) {
                const len = new DataView(chunk.slice(i, i + 2)).getUint16(0);
                ctrl.enqueue(new Uint8Array(chunk.slice(i + 2, i + 2 + len)));
                i += 2 + len;
            }
        }
    });
    ts.readable.pipeTo(new WritableStream({
        async write(pkt) {
            for (const url of DOH_URLS) {
                try {
                    const r = await fetch(url, { method: 'POST', headers: { 'content-type': 'application/dns-message' }, body: pkt });
                    const res = await r.arrayBuffer();
                    const sz = res.byteLength;
                    const szBuf = new Uint8Array([sz >> 8 & 255, sz & 255]);
                    if (ws.readyState === 1) {
                        if (headerSent) ws.send(await new Blob([szBuf, res]).arrayBuffer());
                        else { ws.send(await new Blob([responseHeader, szBuf, res]).arrayBuffer()); headerSent = true; }
                        return;
                    }
                } catch (e) { log(`DoH fail: ${url}`); }
            }
        }
    })).catch(e => log('UDP error', e));
    const w = ts.writable.getWriter();
    return { write: chunk => w.write(chunk) };
}

// ============================================
// MAIN WORKER
// ============================================
export default {
    async fetch(req, env, ctx) {
        userID = env.UUID || env.uuid || userID;
        trojanPass = env.TROJAN_PASS || env.trojan_pass || trojanPass;
        proxyListURL = env.PROXY_LIST_URL || proxyListURL;
        
        const hasVless = isValidUUID(userID);
        const hasTrojan = !!trojanPass;
        
        if (!hasVless && !hasTrojan) {
            return new Response(`<!DOCTYPE html>
<html><head><meta charset="UTF-8"><title>Error</title>
<style>body{font-family:system-ui;background:#0f172a;color:#e2e8f0;display:flex;align-items:center;justify-content:center;height:100vh;margin:0;text-align:center;}
.box{background:#1e293b;padding:40px;border-radius:16px;}h1{color:#f87171;}code{background:#334155;padding:2px 8px;border-radius:4px;}</style></head>
<body><div class="box"><h1>⚠️ Not Configured</h1><p>Set <code>UUID</code> or <code>TROJAN_PASS</code></p></div></body></html>`,
            { status: 500, headers: { 'Content-Type': 'text/html' } });
        }
        
        ctx.waitUntil(refreshProxies());
        
        if (req.headers.get('Upgrade') === 'websocket') {
            return handleWS(req);
        }
        return new Response(getPage(), { status: 200, headers: { 'Content-Type': 'text/html; charset=utf-8' } });
    }
};

// ============================================
// WS HANDLER
// ============================================
async function handleWS(req) {
    const pair = new WebSocketPair();
    const [client, ws] = Object.values(pair);
    ws.accept();
    
    let address = '', portLog = '';
    const log = (info, evt) => console.log(`[${address}:${portLog}] ${info}`, evt || '');
    
    const earlyData = req.headers.get('sec-websocket-protocol') || '';
    const stream = makeWSStream(ws, earlyData, log);
    
    let remote = { value: null };
    let udpWrite = null;
    let isDns = false;
    
    stream.pipeTo(new WritableStream({
        async write(chunk) {
            if (isDns && udpWrite) return udpWrite(chunk);
            if (remote.value) {
                const w = remote.value.writable.getWriter();
                await w.write(chunk); w.releaseLock();
                return;
            }
            const firstByte = new Uint8Array(chunk.slice(0, 1))[0];
            let result = null, proto = 'unknown';
            
            if (firstByte === 0x00 && isValidUUID(userID)) {
                try { result = parseVless(chunk, userID); if (!result.err) proto = 'vless'; } catch (e) { result = { err: e.message }; }
            }
            if ((!result || result.err) && trojanPass) {
                result = parseTrojan(chunk, trojanPass);
                if (result && !result.err) proto = 'trojan';
            }
            if (!result || result.err) throw new Error(result ? result.err : 'Invalid header');
            
            const { addrRemote = '', portRemote = 443, rawIdx, responseHeader, isUDP, addrType } = result;
            address = addrRemote;
            portLog = `${portRemote} ${isUDP ? 'udp' : 'tcp'} [${proto}]`;
            
            if (isUDP && portRemote !== 53) throw new Error('UDP only for DNS port 53');
            if (isUDP && portRemote === 53) isDns = true;
            
            const rawClient = chunk.slice(rawIdx);
            if (isDns) {
                const { write } = await handleUDP(ws, responseHeader, log);
                udpWrite = write; udpWrite(rawClient); return;
            }
            // FIXED: pass addrType to TCP handler (was missing)
            handleTCP(remote, addrRemote, portRemote, rawClient, ws, responseHeader, addrType, log);
        },
        close() { log('WS closed'); },
        abort(r) { log('WS abort', JSON.stringify(r)); }
    })).catch(e => log('Pipe error', e));
    
    return new Response(null, { status: 101, webSocket: client });
}

// ============================================
// GALAXY UI
// ============================================
function getPage() {
    return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Galaxy-Tunnel</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body,html{width:100%;height:100%;background:#02060d;overflow:hidden;font-family:'Segoe UI',Arial,sans-serif;display:flex;justify-content:center;align-items:center}
.space-bg{position:absolute;width:100%;height:100%;background:radial-gradient(circle at 50% 35%,rgba(10,45,80,.7) 0%,transparent 65%),radial-gradient(circle at 80% 80%,rgba(0,150,200,.15) 0%,transparent 50%),#02060d;z-index:1}
.starfield{position:absolute;width:100%;height:100%;background-image:radial-gradient(2px 2px at 20px 30px,#fff,transparent),radial-gradient(2px 2px at 40px 70px,rgba(0,212,255,.8),transparent),radial-gradient(1px 1px at 90px 40px,#fff,transparent),radial-gradient(2px 2px at 160px 120px,rgba(0,212,255,.9),transparent);background-repeat:repeat;background-size:220px 220px;animation:starTwinkle 4s ease-in-out infinite alternate;opacity:.6}
@keyframes starTwinkle{0%{opacity:.4;transform:scale(1)}100%{opacity:.8;transform:scale(1.02)}}
.card-frame{position:relative;z-index:10;width:90vw;max-width:480px;aspect-ratio:1/1;background:rgba(4,12,24,.75);border:1.5px solid rgba(0,212,255,.6);box-shadow:0 0 25px rgba(0,212,255,.25),inset 0 0 25px rgba(0,212,255,.1);backdrop-filter:blur(12px);display:flex;flex-direction:column;justify-content:space-between;align-items:center;padding:35px 25px 25px;border-radius:4px}
.graphic-container{position:relative;width:230px;height:230px;display:flex;justify-content:center;align-items:center}
.ring{position:absolute;width:240px;height:75px;border:2px solid rgba(0,230,255,.85);border-radius:50%;transform:rotate(-28deg);box-shadow:0 0 15px rgba(0,212,255,.8),inset 0 0 15px rgba(0,212,255,.5);pointer-events:none;animation:ringGlow 3s ease-in-out infinite alternate}
@keyframes ringGlow{0%{opacity:.7;box-shadow:0 0 12px rgba(0,212,255,.6)}100%{opacity:1;box-shadow:0 0 25px rgba(0,212,255,1)}}
canvas{position:absolute;top:0;left:0}
.content-bottom{width:100%;display:flex;flex-direction:column;align-items:center;text-align:center;position:relative}
.title{font-size:34px;font-weight:900;font-style:italic;color:#fff;letter-spacing:2px;text-transform:uppercase;text-shadow:0 0 12px rgba(255,255,255,.7);line-height:1.1}
.subtitle{font-size:16px;font-weight:600;color:#7b93a7;letter-spacing:5px;margin-top:6px;text-transform:uppercase}
.access-badge{align-self:flex-end;margin-top:15px;font-size:20px;font-weight:900;font-style:italic;color:#00e5ff;text-transform:uppercase;text-align:right;letter-spacing:1px;line-height:1.1;text-shadow:0 0 15px rgba(0,229,255,.85);animation:statusPulse 2s infinite alternate}
@keyframes statusPulse{0%{opacity:.8;text-shadow:0 0 8px rgba(0,229,255,.5)}100%{opacity:1;text-shadow:0 0 20px rgba(0,229,255,1)}}
</style>
</head>
<body>
<div class="space-bg"></div><div class="starfield"></div>
<div class="card-frame">
<div class="graphic-container"><div class="ring"></div><canvas id="nodeCanvas" width="230" height="230"></canvas></div>
<div class="content-bottom">
<h1 class="title">GALAXY-TUNNEL</h1>
<div class="subtitle">VLESS / TROJAN — RACE DIAL</div>
<div class="access-badge">GALAXY VPROXY<br>IS ACCESS</div>
</div>
</div>
<script>
const canvas=document.getElementById('nodeCanvas'),ctx=canvas.getContext('2d');
const numNodes=32,nodes=[],radius=75;let angleX=.004,angleY=.007;
for(let i=0;i<numNodes;i++){let t=Math.acos(Math.random()*2-1),p=Math.random()*Math.PI*2;nodes.push({x:radius*Math.sin(t)*Math.cos(p),y:radius*Math.sin(t)*Math.sin(p),z:radius*Math.cos(t)})}
function rotX(n,a){let c=Math.cos(a),s=Math.sin(a),y1=n.y*c-n.z*s,z1=n.z*c+n.y*s;n.y=y1;n.z=z1}
function rotY(n,a){let c=Math.cos(a),s=Math.sin(a),x1=n.x*c-n.z*s,z1=n.z*c+n.x*s;n.x=x1;n.z=z1}
function draw(){ctx.clearRect(0,0,230,230);let cx=115,cy=115;nodes.forEach(n=>{rotX(n,angleX);rotY(n,angleY)});ctx.strokeStyle='rgba(0,220,255,.35)';ctx.lineWidth=1;for(let i=0;i<nodes.length;i++)for(let j=i+1;j<nodes.length;j++)if(Math.hypot(nodes[i].x-nodes[j].x,nodes[i].y-nodes[j].y,nodes[i].z-nodes[j].z)<60){ctx.beginPath();ctx.moveTo(nodes[i].x+cx,nodes[i].y+cy);ctx.lineTo(nodes[j].x+cx,nodes[j].y+cy);ctx.stroke()}nodes.forEach(n=>{let sz=(n.z+radius)/(2*radius)*3+2;ctx.beginPath();ctx.arc(n.x+cx,n.y+cy,sz,0,Math.PI*2);ctx.fillStyle='#00f0ff';ctx.shadowBlur=8;ctx.shadowColor='#00f0ff';ctx.fill();ctx.shadowBlur=0});requestAnimationFrame(draw)}draw();
</script>
</body>
</html>`;
}
