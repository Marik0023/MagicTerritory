'use strict';
const express = require('express');
const http    = require('http');
const { Server } = require('socket.io');
const path    = require('path');
const crypto  = require('crypto');

// ─── Config ──────────────────────────────────────────────────────────────────
const PORT       = process.env.PORT       || 3000;
// FIX-1: removed duplicate require('crypto') — crypto already imported on line 6
const ADMIN_KEY  = process.env.ADMIN_KEY  || (() => {
  const generated = crypto.randomBytes(16).toString('hex');
  console.warn(`\n⚠️  ADMIN_KEY not set — generated random key for this session: ${generated}\n`);
  return generated;
})();

const TICK_MS        = 100;   // 10 ticks/sec
const TOTAL_ROUNDS   = 3;
const ROUND_MS       = 5 * 60 * 1000;  // 5 min
const BETWEEN_MS     = 30 * 1000;       // 30 sec between rounds
const COUNTDOWN_MS   = 10 * 1000;       // 10 sec
const KILL_BONUS     = 150;             // score bonus for kill
const START_HALF     = 2;               // starting territory (2*2+1)^2 = 5x5 = 25 cells
const MAX_TRAIL      = 400;             // safety: max trail length before self-kill
const MAX_PLAYERS    = 100;             // hard cap: benchmark shows p95>100ms at 150+ players

// Map size by active player count
function mapSize(n) {
  if (n <= 20)  return 220;
  if (n <= 50)  return 300;
  if (n <= 100) return 380;
  return 520;
}
// Min spawn distance by player count
function spawnRadius(n) {
  if (n <= 50)  return 25;
  if (n <= 100) return 18;
  if (n <= 200) return 12;
  return 9;
}

const DIRS = {
  up:    [0, -1],
  down:  [0,  1],
  left:  [-1, 0],
  right: [1,  0],
};
const OPPOSITE = { up: 'down', down: 'up', left: 'right', right: 'left' };

// ─── Color generation (golden-angle HSL, high saturation, varied lightness) ──
// colorSeq is now per-room (see GameRoom constructor)

// ─── Player ───────────────────────────────────────────────────────────────────
class Player {
  constructor(socketId, sessionId, nickname, color) {
    this.socketId   = socketId;
    this.sessionId  = sessionId;
    this.nickname   = nickname;
    this.color      = color;
    this.playerIndex = 0;      // 1-based, assigned each round

    // Per-round state
    this.x = 0; this.y = 0;
    this.direction   = 'right';
    this.pendingDir  = null;
    this.trail       = [];         // [[x,y], ...]
    this.territory   = new Set();  // cell indices (y*W+x)
    this.alive       = false;
    this.spectator   = false;
    this.joinedMid   = false;      // joined during an active round

    // Scores
    this.roundScore  = 0;
    this.kills       = 0;
    this.totalScore  = 0;
    this.totalKills  = 0;
    this.roundHistory = [];

    // Bot flag
    this.isBot = false;
  }

  // Compact data for broadcast
  pub() {
    return {
      id:    this.socketId,
      sid:   this.sessionId,
      nick:  this.nickname,
      color: this.color,
      pidx:  this.playerIndex,
      x:     this.x,
      y:     this.y,
      dir:   this.direction,
      alive: this.alive,
      spec:  this.spectator,
      score: this.roundScore,
    };
  }
}

// ─── GameRoom ─────────────────────────────────────────────────────────────────
class GameRoom {
  constructor(io) {
    this.io      = io;
    this.players = new Map();   // socketId → Player
    this.sessions = new Map();  // sessionId → Player
    this.state   = 'lobby';     // lobby | countdown | playing | between_rounds | game_over
    this.round   = 0;
    this.W = 220; this.H = 220;
    this.grid    = new Int16Array(220 * 220);
    this.tickTimer      = null;
    this.roundTimer     = null;
    this._countdownTimer = null;
    this._breakTimer    = null;  // between-rounds break + endGame delay
    this.botSeq  = 0;
    this.colorSeq = 0;  // BUG-15 fix: encapsulated per-room
  }

  nextColor() {
    const h = (this.colorSeq++ * 137.508) % 360;
    const l = 50 + (this.colorSeq % 3) * 8;
    return `hsl(${Math.round(h)},80%,${l}%)`;
  }

  // ── Join / Reconnect ───────────────────────────────────────────────────────
  handleJoin(socket, sessionId, rawNickname) {
    // FIX-2a: guard against oversized rawNickname before any string operations
    if (typeof rawNickname !== 'string' || rawNickname.length > 200) return null;

    // Sanitize nickname — preserve original casing, allow a-z A-Z 0-9 _ space
    const nickname = rawNickname
      .replace(/[^a-zA-Z0-9_ ]/g, '')
      .slice(0, 16)
      .trim();
    if (nickname.length < 3) return null;

    const isReconnect = this.sessions.has(sessionId);

    let player;
    if (isReconnect) {
      // Reconnect: same session, new socket — restore existing Player object
      player = this.sessions.get(sessionId);
      if (player.socketId !== socket.id) {
        this.players.delete(player.socketId);
        player.socketId = socket.id;
        this.players.set(socket.id, player);
      }
      // FIX-2b: do NOT override spectator/alive/joinedMid for reconnecting players.
      // An active player who disconnects mid-round and reconnects keeps their
      // in-round state (alive, territory, score). Previously this code always
      // forced spectator=true for any join during 'playing'/'countdown',
      // which silently ejected reconnecting players from the active round.
    } else {
      // Brand-new join
      const color = this.nextColor();
      player = new Player(socket.id, sessionId, nickname, color);
      this.players.set(socket.id, player);
      this.sessions.set(sessionId, player);

      // Determine spectator status for NEW players only
      if (this.state === 'playing' || this.state === 'countdown') {
        player.spectator = true;
        player.joinedMid = true;
      } else {
        player.spectator = false;
        player.joinedMid = false;
      }
    }

    return player;
  }

  handleLeave(socketId) {
    const player = this.players.get(socketId);
    if (!player) return;

    // FIX-3: Previously only cleared trail (and only when trail.length > 0),
    // leaving ghost territory on the grid when a player disconnected inside
    // their own territory. Now mirrors the full death sequence from tick():
    // clear trail → wipe territory from grid → emit died.
    if (player.alive) {
      const dirty = new Map();

      // Clear any active trail
      const cleared = this.clearTrail(player, null);
      for (const [ci, val] of cleared) dirty.set(ci, val);

      // Wipe the player's entire territory from the grid
      for (const ci of player.territory) {
        if (this.grid[ci] === player.playerIndex) {
          this.grid[ci] = 0;
          dirty.set(ci, 0);
        }
      }
      player.territory.clear();
      player.alive = false;

      this.broadcastDirty(dirty);
      this.io.emit('died', { id: socketId, nick: player.nickname });
    }

    this.players.delete(socketId);
    // Keep session entry for potential reconnect
    this.io.emit('p_left', { id: socketId });
  }

  handleDir(socketId, dir) {
    if (!DIRS[dir]) return;
    const player = this.players.get(socketId);
    if (!player || !player.alive || player.spectator) return;
    if (dir === OPPOSITE[player.direction]) return; // can't reverse
    player.pendingDir = dir;
  }

  // ── Admin ─────────────────────────────────────────────────────────────────
  adminStart() {
    if (this.state !== 'lobby') return { ok: false, error: 'Not in lobby' };
    // FIX-4: reuse humanPlayers instead of recalculating count separately
    const humanPlayers = [...this.players.values()].filter(p => !p.spectator).length;
    if (humanPlayers === 0) return { ok: false, error: 'No players in lobby' };
    this.round = 0;
    this.state = 'countdown';
    this.io.emit('countdown', { secs: COUNTDOWN_MS / 1000, players: humanPlayers });
    this._breakTimer = setTimeout(() => this.startRound(), COUNTDOWN_MS);
    return { ok: true };
  }

  adminReset() {
    this.stopTimers();
    this.players.clear();
    this.sessions.clear();
    this.colorSeq = 0;  // BUG-15 fix: was global colorSeq = 0
    this.state = 'lobby';
    this.round = 0;
    this.W = 220; this.H = 220;
    this.grid = new Int16Array(this.W * this.H);  // BUG-01 fix: was incorrectly Int16Array with only 1 element
    this.io.emit('reset');
    return { ok: true };
  }

  addBots(count) {
    if (this.state === 'playing') {
      return { ok: false, error: 'Cannot add bots during an active round. Wait for between_rounds or lobby.' };
    }
    // FIX-5: track actual number added (may be less than requested due to MAX_PLAYERS cap)
    let added = 0;
    for (let i = 0; i < count; i++) {
      // SEC-04 guard: respect max players cap
      if (this.players.size >= MAX_PLAYERS) break;
      const id = `bot_${++this.botSeq}`;
      const sid = `bot_sess_${this.botSeq}`;
      const nick = `bot${this.botSeq}`;
      const color = this.nextColor();
      const p = new Player(id, sid, nick, color);
      p.isBot = true;
      this.players.set(id, p);
      this.sessions.set(sid, p);
      // Notify all connected clients about this bot
      this.io.emit('p_joined', p.pub());
      added++;
    }
    return { ok: true, bots: added };
  }

  // ── Round lifecycle ───────────────────────────────────────────────────────
  startRound() {
    // Only clear game timers, not _breakTimer (it already fired to call us)
    if (this.tickTimer)  { clearInterval(this.tickTimer);  this.tickTimer  = null; }
    if (this.roundTimer) { clearTimeout(this.roundTimer);  this.roundTimer = null; }
    this._breakTimer     = null;
    this._countdownTimer = null;
    this.round++;

    // BUG-02 fix: clear joinedMid for ALL players so countdown-joiners can participate in round 1
    // Activate waiting players (were spectator from lobby → now active)
    for (const p of this.players.values()) {
      // FIX-6: merged two conditions — spectator is only ever true when joinedMid is also true,
      // so the second branch (spectator && !joinedMid) was dead code. Unified into one check.
      if (p.spectator) { p.spectator = false; p.joinedMid = false; }
      p.alive = false;
      p.trail = [];
      p.territory = new Set();
      p.roundScore = 0;
      p.kills = 0;
      p.isSurvivor = false;  // NEW-03 fix: defensive reset in case of state corruption
    }

    const active = [...this.players.values()].filter(p => !p.spectator);
    if (active.length === 0) {
      // No players → back to lobby
      this.state = 'lobby';
      this.round = 0;
      return;
    }

    this.W = this.H = mapSize(active.length);
    this.grid = new Int16Array(this.W * this.H);

    // Assign indices + spawn
    const spawnPoints = [];
    let idx = 1;
    for (const p of active) {
      p.playerIndex = idx++;
      p.alive = true;
      p.direction = ['up','down','left','right'][Math.floor(Math.random() * 4)];
      p.pendingDir = null;
      this.spawnPlayer(p, spawnPoints);
      spawnPoints.push([p.x, p.y]);
    }

    this.state = 'playing';

    this.io.emit('round_start', {
      round: this.round,
      total: TOTAL_ROUNDS,
      W: this.W,
      H: this.H,
      grid: Array.from(this.grid),
      players: [...this.players.values()].map(p => p.pub()),
      duration: ROUND_MS,
      serverStartedAt: Date.now(),  // BUG-M02 fix: client uses this to compensate for lag
    });

    this.tickTimer  = setInterval(() => this.tick(), TICK_MS);
    this.roundTimer = setTimeout(() => this.endRound(), ROUND_MS);
  }

  spawnPlayer(player, existingPoints) {
    const margin = START_HALF + 3;
    let R = spawnRadius(existingPoints.length + 1);

    const trySpawn = () => {
      for (let attempt = 0; attempt < 2000; attempt++) {
        const x = margin + Math.floor(Math.random() * (this.W - 2 * margin));
        const y = margin + Math.floor(Math.random() * (this.H - 2 * margin));
        let ok = true;
        for (const [ex, ey] of existingPoints) {
          const dx = x - ex, dy = y - ey;
          if (dx * dx + dy * dy < R * R) { ok = false; break; }
        }
        if (ok) return [x, y];
      }
      return null;
    };

    let pos = null;
    while (!pos) {
      pos = trySpawn();
      if (!pos) R = Math.max(1, R - 1);
    }

    player.x = pos[0];
    player.y = pos[1];

    // 5×5 starting territory
    for (let dy = -START_HALF; dy <= START_HALF; dy++) {
      for (let dx = -START_HALF; dx <= START_HALF; dx++) {
        const cx = player.x + dx, cy = player.y + dy;
        if (cx >= 0 && cx < this.W && cy >= 0 && cy < this.H) {
          const ci = cy * this.W + cx;
          player.territory.add(ci);
          this.grid[ci] = player.playerIndex;
        }
      }
    }
  }

  // ── Game tick ─────────────────────────────────────────────────────────────
  tick() {
    if (this.state !== 'playing') return;

    // Run bot AI first
    for (const p of this.players.values()) {
      if (p.isBot && p.alive) this.botAI(p);
    }

    const dirty  = new Map();
    const toKill = new Set();
    const toCapture = [];

    const alive = [...this.players.values()].filter(p => p.alive && !p.spectator);

    // FIX-7: build O(1) playerIndex → Player map once per tick.
    // Previously _findByIndex() and .find() were called inside per-player loops,
    // making trail-collision and territory-overwrite O(N²) at scale.
    const playerByIdx = new Map(alive.map(p => [p.playerIndex, p]));

    // Apply pending direction changes
    for (const p of alive) {
      if (p.pendingDir && p.pendingDir !== OPPOSITE[p.direction]) {
        p.direction = p.pendingDir;
      }
      p.pendingDir = null;
    }

    // Compute new positions
    const moves = new Map(); // socketId → {nx, ny}
    for (const p of alive) {
      const [dx, dy] = DIRS[p.direction];
      moves.set(p.socketId, { nx: p.x + dx, ny: p.y + dy });
    }

    // Build current trail map for collision detection
    const trailMap = new Map(); // cellIndex → playerIndex (owner)
    for (const p of alive) {
      for (const [tx, ty] of p.trail) {
        trailMap.set(ty * this.W + tx, p.playerIndex);
      }
    }

    // Detect collisions
    for (const p of alive) {
      if (toKill.has(p.socketId)) continue;
      const { nx, ny } = moves.get(p.socketId);

      // Wall
      if (nx < 0 || nx >= this.W || ny < 0 || ny >= this.H) {
        toKill.add(p.socketId); continue;
      }

      // Own trail
      const nci = ny * this.W + nx;
      const trailOwner = trailMap.get(nci);
      if (trailOwner === p.playerIndex) {
        toKill.add(p.socketId); continue;
      }

      // Enemy trail → trail OWNER dies (their line was cut), crosser survives and gets credit
      if (trailOwner !== undefined && trailOwner !== p.playerIndex) {
        // FIX-7: was [...this.players.values()].find(...) — O(N) scan; now O(1) map lookup
        const victim = playerByIdx.get(trailOwner);
        if (victim && victim.alive && !toKill.has(victim.socketId)) {
          toKill.add(victim.socketId);
          p.kills++;
          // BUG-04 fix: removed redundant p.roundScore += KILL_BONUS here.
          // Score is fully recalculated at end of tick as: territory.size + kills * KILL_BONUS
        }
        // p continues moving — do NOT add p to toKill
        continue;
      }

      // Safety: trail too long
      if (p.trail.length >= MAX_TRAIL) {
        toKill.add(p.socketId); continue;
      }
    }

    // Two heads on same cell → both die
    const headCells = new Map(); // cellIndex → [socketId, ...]
    for (const p of alive) {
      if (toKill.has(p.socketId)) continue;
      const { nx, ny } = moves.get(p.socketId);
      const ci = ny * this.W + nx;
      if (!headCells.has(ci)) headCells.set(ci, []);
      headCells.get(ci).push(p.socketId);
    }
    for (const [, ids] of headCells) {
      if (ids.length > 1) ids.forEach(id => toKill.add(id));
    }

    // Apply moves to surviving players
    for (const p of alive) {
      if (toKill.has(p.socketId)) continue;
      const { nx, ny } = moves.get(p.socketId);
      const ci = ny * this.W + nx;

      // FIX-8 (unused vars): removed unused prevX / prevY variables
      p.x = nx; p.y = ny;

      if (p.territory.has(ci) && p.trail.length > 0) {
        // Returned home → capture
        // Add trail to territory first
        for (const [tx, ty] of p.trail) {
          const tci = ty * this.W + tx;
          p.territory.add(tci);
          this.grid[tci] = p.playerIndex;
          dirty.set(tci, p.playerIndex);
        }
        p.trail = [];
        toCapture.push(p);
      } else if (!p.territory.has(ci)) {
        // Going out → add to trail
        p.trail.push([nx, ny]);
        // ── Remove from previous owner's territory Set ──────────────────────
        // When drawing over another player's territory, their Set must not retain
        // this cell — otherwise their flood-fill treats it as a barrier and the
        // dead player's territory visually persists after we clear the trail.
        const prevVal = this.grid[ci];
        if (prevVal > 0) {
          // FIX-7: was this._findByIndex(prevVal) — O(N); now O(1) map lookup
          const prevOwner = playerByIdx.get(prevVal);
          if (prevOwner) prevOwner.territory.delete(ci);
        }
        // ────────────────────────────────────────────────────────────────────
        this.grid[ci] = -p.playerIndex; // trail marker
        dirty.set(ci, -p.playerIndex);
      }
      // else: moving within own territory, no trail change needed
    }

    // Flood-fill captures
    for (const p of toCapture) {
      if (!p.alive) continue;
      const changed = this.floodCapture(p, playerByIdx);
      for (const [ci, val] of changed) dirty.set(ci, val);
    }

    // If a player's trail cell was captured by someone else, kill them
    for (const p of alive) {
      if (toKill.has(p.socketId) || !p.alive) continue;
      for (const [tx, ty] of p.trail) {
        const tci = ty * this.W + tx;
        if (this.grid[tci] > 0 && this.grid[tci] !== p.playerIndex) {
          // Trail was consumed by flood fill → die
          toKill.add(p.socketId);
          break;
        }
      }
    }

    // Process deaths
    for (const socketId of toKill) {
      const p = this.players.get(socketId);
      if (!p || !p.alive) continue;
      p.alive = false;
      // Помер — зберігає 50% territory score + всі кіли
      p.roundScore = Math.round(p.territory.size * 0.5) + p.kills * KILL_BONUS;
      const cleared = this.clearTrail(p, playerByIdx);
      for (const [ci, val] of cleared) dirty.set(ci, val);
      // ── Wipe the dead player's entire territory ──────────────────────────
      for (const ci of p.territory) {
        const cur = this.grid[ci];
        if (cur === p.playerIndex) {
          this.grid[ci] = 0;
          dirty.set(ci, 0);
        } else {
          dirty.set(ci, cur);
        }
      }
      p.territory.clear();
      // ─────────────────────────────────────────────────────────────────────
      this.io.emit('died', { id: p.socketId, nick: p.nickname });
    }

    // Update round scores for alive players (territory + kills)
    // Track meaningful deltas (≥5 pts) for floating indicators — ignores single-cell moves
    const scoreDeltas = [];
    for (const p of alive) {
      if (p.alive) {
        const prev = p.roundScore;
        p.roundScore = p.territory.size + p.kills * KILL_BONUS;
        const delta = p.roundScore - prev;
        if (Math.abs(delta) >= 5) scoreDeltas.push({ id: p.socketId, delta, x: p.x, y: p.y, color: p.color });
      }
    }

    // Check if round should end:
    //  - 1 player remains from a multi-player round → that player wins
    //  - 0 players remain → tie/end
    const stillAlive = alive.filter(p => p.alive);
    if (stillAlive.length <= 1 && alive.length >= 2) {
      // Mark the survivor — bonus will be applied in endRound() AFTER rank multiplier (BUG-C02 fix)
      if (stillAlive.length === 1) {
        stillAlive[0].isSurvivor = true;
      }
      clearInterval(this.tickTimer);
      clearTimeout(this.roundTimer);
      this.tickTimer = null;
      this.roundTimer = null;
      setTimeout(() => this.endRound(), 300);
      return;
    }

    // Broadcast
    const ci = []; const cv = [];
    for (const [k, v] of dirty) { ci.push(k); cv.push(v); }

    this.io.emit('tick', {
      ci,  // dirty cell indices
      cv,  // dirty cell values
      p: [...this.players.values()].map(p => ({
        id: p.socketId,
        x: p.x, y: p.y,
        dir: p.direction,
        alive: p.alive,
        score: p.roundScore,
        total: p.totalScore,  // BUG-N05 fix: broadcast running total
      })),
      lb: this.topN(5),
      sd: scoreDeltas,  // score deltas for floating indicators
    });
  }

  // Flood-fill from borders; everything not reachable = inside = captured by player
  floodCapture(player, playerByIdx) {
    const W = this.W, H = this.H, size = W * H;
    const outside = new Uint8Array(size);
    const queue   = [];

    // BUG-05 fix: build O(1) lookup — reuse passed-in map when available (PERF-02 fix)
    if (!playerByIdx) {
      playerByIdx = new Map([...this.players.values()].map(p => [p.playerIndex, p]));
    }

    const seed = (ci) => {
      if (!outside[ci] && !player.territory.has(ci)) {
        outside[ci] = 1;
        queue.push(ci);
      }
    };

    for (let x = 0; x < W; x++) { seed(x); seed((H-1)*W + x); }
    for (let y = 1; y < H-1; y++) { seed(y*W); seed(y*W + W-1); }

    let qi = 0;
    while (qi < queue.length) {
      const ci = queue[qi++];
      const x = ci % W, y = (ci / W) | 0;
      if (x > 0)   { const n = ci-1;   if (!outside[n] && !player.territory.has(n)) { outside[n]=1; queue.push(n); } }
      if (x < W-1) { const n = ci+1;   if (!outside[n] && !player.territory.has(n)) { outside[n]=1; queue.push(n); } }
      if (y > 0)   { const n = ci-W;   if (!outside[n] && !player.territory.has(n)) { outside[n]=1; queue.push(n); } }
      if (y < H-1) { const n = ci+W;   if (!outside[n] && !player.territory.has(n)) { outside[n]=1; queue.push(n); } }
    }

    const changes = new Map();
    for (let ci = 0; ci < size; ci++) {
      if (!outside[ci] && !player.territory.has(ci)) {
        // Remove from previous owner's territory Set (BUG-05: use O(1) map lookup)
        const prev = this.grid[ci];
        if (prev > 0) {
          const owner = playerByIdx.get(prev);
          if (owner) owner.territory.delete(ci);
        } else if (prev < 0) {
          const trailOwner = playerByIdx.get(-prev);
          if (trailOwner) trailOwner.territory.delete(ci);
        }
        player.territory.add(ci);
        this.grid[ci] = player.playerIndex;
        changes.set(ci, player.playerIndex);
      }
    }
    return changes;
  }

  clearTrail(player, playerByIdx) {
    const changes = new Map();
    for (const [tx, ty] of player.trail) {
      const ci = ty * this.W + tx;
      if (this.grid[ci] === -player.playerIndex) {
        // Safety: if another player still claims this cell in their territory Set, restore it.
        // This can happen in edge-case simultaneous events.
        let restored = false;
        // Use playerByIdx O(1) map when available, fallback to full scan
        if (playerByIdx) {
          // Grid value here is -player.playerIndex (trail), so check adjacent owners via territory
          // We still need a scan here for territory membership; optimise via grid ownership where possible
          for (const other of playerByIdx.values()) {
            if (other.socketId !== player.socketId && other.territory.has(ci)) {
              this.grid[ci] = other.playerIndex;
              changes.set(ci, other.playerIndex);
              restored = true;
              break;
            }
          }
        } else {
          for (const other of this.players.values()) {
            if (other.socketId !== player.socketId && other.territory.has(ci)) {
              this.grid[ci] = other.playerIndex;
              changes.set(ci, other.playerIndex);
              restored = true;
              break;
            }
          }
        }
        if (!restored) {
          this.grid[ci] = 0;
          changes.set(ci, 0);
        }
      }
    }
    player.trail = [];
    return changes;
  }

  broadcastDirty(map) {
    if (map.size === 0) return;
    const ci = [], cv = [];
    for (const [k, v] of map) { ci.push(k); cv.push(v); }
    this.io.emit('dirty', { ci, cv });
  }

  _findByIndex(pidx) {
    for (const p of this.players.values()) {
      if (p.playerIndex === pidx) return p;
    }
    return null;
  }

  // ── Bot AI ────────────────────────────────────────────────────────────────
  botAI(bot) {
    const W = this.W, H = this.H;

    // PERF-01 fix: build O(1) Set for trail membership checks (was O(trail_len) linear scan)
    const trailSet = new Set(bot.trail.map(([tx, ty]) => ty * W + tx));

    // Helper: is a cell safe for the bot to step on?
    const isSafe = (x, y, checkEscape = false) => {
      if (x < 1 || x >= W - 1 || y < 1 || y >= H - 1) return false;
      // Own trail → danger (O(1) lookup via Set)
      if (trailSet.has(y * W + x)) return false;
      // Check escape routes if requested
      if (checkEscape) {
        let exits = 0;
        for (const [ddx, ddy] of Object.values(DIRS)) {
          const nx2 = x + ddx, ny2 = y + ddy;
          if (nx2 < 1 || nx2 >= W-1 || ny2 < 1 || ny2 >= H-1) continue;
          if (!trailSet.has(ny2 * W + nx2)) exits++;
        }
        return exits >= 2;
      }
      return true;
    };

    const [dx, dy] = DIRS[bot.direction];
    const frontSafe = isSafe(bot.x + dx, bot.y + dy, true);

    // Return home if trail too long — navigate toward nearest territory cell
    if (bot.trail.length > 28) {
      let bestDir = null, bestDist = Infinity;
      for (const [dir, [ddx, ddy]] of Object.entries(DIRS)) {
        if (dir === OPPOSITE[bot.direction]) continue;
        const cx = bot.x + ddx, cy = bot.y + ddy;
        if (!isSafe(cx, cy)) continue;
        for (const ci of bot.territory) {
          const tx = ci % W, ty = (ci / W) | 0;
          const dist = Math.abs(tx - cx) + Math.abs(ty - cy);
          if (dist < bestDist) { bestDist = dist; bestDir = dir; }
          if (bestDist < 4) break;
        }
      }
      if (bestDir) { bot.pendingDir = bestDir; return; }
    }

    if (!frontSafe) {
      // Try perpendicular turns first (shuffled)
      const perp = (bot.direction === 'up' || bot.direction === 'down')
        ? ['left', 'right'] : ['up', 'down'];
      if (Math.random() < 0.5) perp.reverse();
      for (const d of perp) {
        const [ddx, ddy] = DIRS[d];
        if (isSafe(bot.x + ddx, bot.y + ddy, true)) {
          bot.pendingDir = d;
          return;
        }
      }
      // Last resort: any safe direction
      for (const [d, [ddx, ddy]] of Object.entries(DIRS)) {
        if (d === OPPOSITE[bot.direction]) continue;
        if (isSafe(bot.x + ddx, bot.y + ddy)) {
          bot.pendingDir = d;
          return;
        }
      }
    } else if (Math.random() < 0.035) {
      // Occasionally expand in a perpendicular direction
      const perp = (bot.direction === 'up' || bot.direction === 'down')
        ? ['left', 'right'] : ['up', 'down'];
      const d = perp[Math.floor(Math.random() * 2)];
      const [ddx, ddy] = DIRS[d];
      if (isSafe(bot.x + ddx, bot.y + ddy, true)) bot.pendingDir = d;
    }
  }

  // ── Round end ─────────────────────────────────────────────────────────────
  endRound() {
    this.stopTimers();
    this.state = 'between_rounds';

    // BUG-C01 fix: sort active players — alive players ALWAYS outrank dead ones,
    // regardless of score. Within each group, sort by roundScore descending.
    const activePlayers = [...this.players.values()]
      .filter(p => !p.spectator)
      .sort((a, b) => {
        if (a.alive !== b.alive) return (b.alive ? 1 : 0) - (a.alive ? 1 : 0);
        return b.roundScore - a.roundScore;
      });

    // Apply rank bonuses based on corrected ordering
    activePlayers.forEach((p, i) => {
      const rank = i + 1;
      let multiplier = 1.0;
      if      (rank === 1) multiplier = 1.20;
      else if (rank === 2) multiplier = 1.10;
      else if (rank === 3) multiplier = 1.05;
      p.roundScore = Math.round(p.roundScore * multiplier);
    });

    // BUG-C02 fix: add survival bonus AFTER rank multiplier so it isn't amplified
    for (const p of activePlayers) {
      if (p.isSurvivor) {
        p.roundScore += 400;
        p.isSurvivor = false;
      }
    }

    // BUG-N05 / NEW-01 fix: accumulate FIRST so totalSoFar includes the current round
    for (const p of this.players.values()) {
      p.totalScore += p.roundScore;
      p.totalKills += p.kills;
      p.roundHistory.push(p.roundScore);
    }

    const scores = [...this.players.values()]
      .filter(p => !p.isBot || p.roundScore > 0)
      .map(p => ({
        id:         p.socketId,
        sid:        p.sessionId,
        nick:       p.nickname,
        color:      p.color,
        score:      p.roundScore,
        kills:      p.kills,
        totalSoFar: p.totalScore, // now correct — includes current round
      }))
      .sort((a, b) => b.score - a.score);

    if (this.round >= TOTAL_ROUNDS) {
      // BUG-C03 fix: show round results for the final round before going to game_over
      this.io.emit('round_end', {
        round:     this.round,
        total:     TOTAL_ROUNDS,
        scores:    scores.slice(0, 10),
        allScores: scores,
        hasNext:   false,
        nextIn:    0,
      });
      // Brief delay so players can read the final round scores before the game_over overlay
      this._breakTimer = setTimeout(() => this.endGame(), 5000);
    } else {
      this.io.emit('round_end', {
        round:     this.round,
        total:     TOTAL_ROUNDS,
        scores:    scores.slice(0, 10),
        allScores: scores,
        hasNext:   true,
        nextIn:    BETWEEN_MS / 1000,
      });

      // BUG-03 fix: use BETWEEN_MS constant instead of hardcoded 30_000
      this._breakTimer = setTimeout(() => {
        if (this.state !== 'between_rounds') return;
        for (const p of this.players.values()) {
          if (p.joinedMid) { p.spectator = false; p.joinedMid = false; }
        }
        this.startRound();
      }, BETWEEN_MS);
    }
  }

  endGame() {
    this.state = 'game_over';
    const final = [...this.players.values()]
      .sort((a, b) => b.totalScore - a.totalScore)
      .map((p, i) => ({
        rank:       i + 1,
        sid:        p.sessionId,
        nick:       p.nickname,
        color:      p.color,
        total:      p.totalScore,
        totalKills: p.totalKills,
        rounds:     p.roundHistory,
      }));
    this.io.emit('game_over', { scores: final });
    // No auto-reset — leaderboard stays until admin manually resets
  }

  // ── Leaderboard ───────────────────────────────────────────────────────────
  topN(n) {
    return [...this.players.values()]
      .filter(p => !p.spectator)
      // NEW-02 fix: alive players always shown above dead (same as endRound ranking)
      .sort((a, b) => {
        if (a.alive !== b.alive) return (b.alive ? 1 : 0) - (a.alive ? 1 : 0);
        return b.roundScore - a.roundScore;
      })
      .slice(0, n)
      .map(p => ({ nick: p.nickname, color: p.color, score: p.roundScore, alive: p.alive }));
  }

  // ── Helpers ───────────────────────────────────────────────────────────────
  stopTimers() {
    if (this.tickTimer)       { clearInterval(this.tickTimer);        this.tickTimer        = null; }
    if (this.roundTimer)      { clearTimeout(this.roundTimer);        this.roundTimer       = null; }
    if (this._countdownTimer) { clearTimeout(this._countdownTimer);   this._countdownTimer  = null; }
    if (this._breakTimer)     { clearTimeout(this._breakTimer);       this._breakTimer      = null; }
  }

  currentStateFor(player) {
    return {
      state:   this.state,
      round:   this.round,
      total:   TOTAL_ROUNDS,
      W:       this.W,
      H:       this.H,
      grid:    Array.from(this.grid),
      players: [...this.players.values()].map(p => p.pub()),
      me:      player.pub(),
    };
  }
}

// ─── Express + Socket.io setup ────────────────────────────────────────────────
const app    = express();
const server = http.createServer(app);
const io     = new Server(server, {
  cors:           { origin: process.env.ALLOWED_ORIGIN || '*' },
  pingInterval:   10000,
  pingTimeout:    20000,
});

const room = new GameRoom(io);

app.use(express.json());
app.use(express.static(path.join(__dirname)));

// Explicit root route for clarity
app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'index.html'));
});

// ─── Admin HTTP API ────────────────────────────────────────────────────────────
function adminAuth(req, res, next) {
  const key = req.query.key || req.headers['x-admin-key'] || req.body?.key;
  if (key !== ADMIN_KEY) return res.status(403).json({ error: 'Forbidden' });
  next();
}

app.post('/api/admin/start',      adminAuth, (req, res) => res.json(room.adminStart()));
app.post('/api/admin/reset',      adminAuth, (req, res) => res.json(room.adminReset()));
app.post('/api/admin/bots',       adminAuth, (req, res) => {
  const n = Math.min(20, Math.max(1, parseInt(req.body.count) || 5));
  res.json(room.addBots(n));
});
app.get('/api/admin/status',      adminAuth, (req, res) => {
  res.json({
    state:   room.state,
    round:   room.round,
    players: [...room.players.values()].map(p => ({
      nick:   p.nickname,
      score:  p.roundScore,
      alive:  p.alive,
      spec:   p.spectator,
      bot:    p.isBot,
    })),
  });
});

// Admin panel HTML — SEC-02 fix: key no longer injected into page source
app.get('/admin', (req, res) => {
  if (req.query.key !== ADMIN_KEY && req.headers['x-admin-key'] !== ADMIN_KEY) {
    return res.status(403).send(`
    <html><body style="background:#0d0d1e;color:#fff;font-family:sans-serif;display:flex;align-items:center;justify-content:center;height:100vh">
    <div><h2>Access Denied</h2><p>Provide <code>?key=</code> parameter or <code>x-admin-key</code> header</p></div>
    </body></html>`);
  }

  // SEC-02 fix: key is NOT embedded into the page JS.
  // Instead the admin panel stores it in sessionStorage after a login prompt.
  res.send(`<!DOCTYPE html>
<html><head><meta charset="UTF-8"><title>Admin Panel</title>
<style>
  * { margin:0;padding:0;box-sizing:border-box; }
  body { background:#0d0d1e;color:#e8e8f0;font-family:'Segoe UI',sans-serif;padding:30px; }
  h1 { font-size:1.8em;margin-bottom:20px;color:#4d96ff; }
  .card { background:rgba(255,255,255,.05);border:1px solid rgba(255,255,255,.1);border-radius:12px;padding:20px;margin-bottom:15px; }
  .btn { padding:10px 20px;border:none;border-radius:8px;cursor:pointer;font-size:.95em;font-weight:700;margin:5px;transition:.2s; }
  .btn:hover { opacity:.8; }
  .start  { background:#22c55e;color:#fff; }
  .reset  { background:#ef4444;color:#fff; }
  .bots   { background:#f59e0b;color:#fff; }
  .status { background:rgba(255,255,255,.05);border-radius:8px;padding:15px;font-size:.85em;white-space:pre-wrap;font-family:monospace;max-height:300px;overflow-y:auto;margin-top:15px; }
  input[type=number] { background:rgba(255,255,255,.1);border:1px solid rgba(255,255,255,.2);border-radius:6px;padding:8px 12px;color:#fff;width:80px;margin:5px; }
  input[type=password] { background:rgba(255,255,255,.1);border:1px solid rgba(255,255,255,.2);border-radius:6px;padding:8px 12px;color:#fff;width:220px;margin:5px; }
  label { color:rgba(255,255,255,.6);font-size:.9em; }
  h3 { color:rgba(255,255,255,.6);font-size:.8em;text-transform:uppercase;letter-spacing:1px;margin-bottom:10px; }
  #login-card { display:flex;align-items:center;gap:10px;flex-wrap:wrap; }
</style>
</head><body>
<h1>🎮 Territory.io — Admin</h1>

<div class="card">
  <h3>Authentication</h3>
  <div id="login-card">
    <label>Admin Key: <input type="password" id="keyInput" placeholder="Enter admin key"></label>
    <button class="btn" style="background:#4d96ff;color:#fff" onclick="saveKey()">🔑 Authenticate</button>
    <span id="auth-status" style="font-size:.8em;color:rgba(255,255,255,.4)"></span>
  </div>
</div>

<div class="card">
  <h3>Game Control</h3>
  <button class="btn start" onclick="api('start')">▶ Start Game</button>
  <button class="btn reset" onclick="api('reset')">↺ Reset</button>
</div>

<div class="card">
  <h3>Bots</h3>
  <label>Count: <input type="number" id="botCount" value="5" min="1" max="20"></label>
  <button class="btn bots" onclick="addBots()">🤖 Add Bots</button>
</div>

<div class="card">
  <h3>Status <span style="float:right;cursor:pointer;opacity:.5" onclick="refresh()">↻ Refresh</span></h3>
  <div id="status" class="status">Enter admin key above, then refresh.</div>
</div>

<script>
  // SEC-02 fix: key stored in sessionStorage only (not in page source)
  function getKey() { return sessionStorage.getItem('adminKey') || ''; }
  function saveKey() {
    const k = document.getElementById('keyInput').value.trim();
    sessionStorage.setItem('adminKey', k);
    document.getElementById('auth-status').textContent = '✓ Key saved for this session';
    refresh();
  }

  async function api(action) {
    const r = await fetch('/api/admin/' + action, {
      method: 'POST',
      headers: {'Content-Type':'application/json','x-admin-key': getKey()},
      body: JSON.stringify({})
    });
    const d = await r.json();
    alert(JSON.stringify(d));
    refresh();
  }
  async function addBots() {
    const n = document.getElementById('botCount').value;
    const r = await fetch('/api/admin/bots', {
      method: 'POST',
      headers: {'Content-Type':'application/json','x-admin-key': getKey()},
      body: JSON.stringify({count: +n})
    });
    const d = await r.json();
    alert(JSON.stringify(d));
    refresh();
  }
  async function refresh() {
    const r = await fetch('/api/admin/status', { headers: {'x-admin-key': getKey()} });
    if (!r.ok) { document.getElementById('status').textContent = 'Auth failed — enter correct key above.'; return; }
    const d = await r.json();
    document.getElementById('status').textContent = JSON.stringify(d, null, 2);
  }
  setInterval(refresh, 5000);
</script>
</body></html>`);
});

// ─── Socket.io events ─────────────────────────────────────────────────────────
const dirRateLimit  = new Map(); // socketId → {count, ts}
const joinRateLimit = new Map(); // ip → {count, ts}  BUG-13 fix

// FIX-9: periodically evict expired joinRateLimit entries to prevent memory growth
// (one entry per unique IP accumulates indefinitely without cleanup)
setInterval(() => {
  const cutoff = Date.now() - 10000;
  for (const [ip, entry] of joinRateLimit) {
    if (entry.ts < cutoff) joinRateLimit.delete(ip);
  }
}, 60 * 1000); // clean up every minute

io.on('connection', socket => {
  console.log(`[connect] ${socket.id}`);

  socket.on('join', ({ nickname, sessionId }) => {
    // FIX-10: explicit type + length guards before any string processing
    // (a 10 MB nickname string would be sliced inside handleJoin but still
    //  allocate memory before the slice — reject early here instead)
    if (typeof nickname !== 'string' || typeof sessionId !== 'string') return;
    if (nickname.length > 200 || sessionId.length > 200) return;
    if (!/^[a-z0-9_]{8,40}$/.test(sessionId)) return;

    // BUG-13 fix: rate limit join events per IP (max 5 joins per 10s)
    const ip  = socket.handshake.address;
    const now = Date.now();
    let jrl   = joinRateLimit.get(ip);
    if (!jrl || now - jrl.ts > 10000) { jrl = { count: 0, ts: now }; joinRateLimit.set(ip, jrl); }
    jrl.count++;
    if (jrl.count > 5) { socket.emit('err', { msg: 'Too many join attempts. Please wait.' }); return; }

    // SEC-04 fix: enforce max players cap
    if (room.players.size >= MAX_PLAYERS && !room.sessions.has(sessionId)) {
      socket.emit('err', { msg: 'Server is full. Please try again later.' });
      return;
    }

    const player = room.handleJoin(socket, sessionId, nickname);
    if (!player) {
      socket.emit('err', { msg: 'Invalid nickname' });
      return;
    }

    socket.emit('joined', room.currentStateFor(player));
    // Notify others
    socket.broadcast.emit('p_joined', player.pub());
    // Broadcast lobby player count update
    if (room.state === 'lobby') {
      room.io.emit('lobby_update', {
        players: [...room.players.values()].map(p => p.pub()),
      });
    }
    console.log(`[join] ${player.nickname} (${player.sessionId.slice(0,8)}...) spec=${player.spectator}`);
  });

  socket.on('dir', (dir) => {
    // FIX-11: type-guard dir input — malformed payload (null, object, number) must not reach handleDir
    if (typeof dir !== 'string') return;
    // Rate limit: max 20 direction changes per second
    const now = Date.now();
    let rl = dirRateLimit.get(socket.id);
    if (!rl || now - rl.ts > 1000) {
      rl = { count: 0, ts: now };
      dirRateLimit.set(socket.id, rl);
    }
    rl.count++;
    if (rl.count > 20) return;
    room.handleDir(socket.id, dir);
  });

  socket.on('disconnect', () => {
    room.handleLeave(socket.id);
    dirRateLimit.delete(socket.id);
    // Note: joinRateLimit is keyed by IP, intentionally kept across connections
    console.log(`[disconnect] ${socket.id}`);
  });
});

server.listen(PORT, () => {
  const isProd = process.env.NODE_ENV === 'production';
  console.log(`\n🎮 Territory.io running on http://localhost:${PORT}`);

  // SEC-04 fix: don't expose full admin URL with key in production logs
  if (isProd) {
    console.log(`🔑 Admin panel: http://localhost:${PORT}/admin  (set ADMIN_KEY env var)`);
  } else {
    console.log(`🔑 Admin panel: http://localhost:${PORT}/admin?key=${ADMIN_KEY}`);
  }

  // SEC-03 fix: warn if CORS wildcard is active
  if (!process.env.ALLOWED_ORIGIN) {
    console.warn(`⚠️  ALLOWED_ORIGIN not set — CORS is open (*). Set ALLOWED_ORIGIN in production.\n`);
  }
});
