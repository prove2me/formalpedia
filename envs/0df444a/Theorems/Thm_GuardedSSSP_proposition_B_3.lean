-- Prove2me | Theorems.Thm_GuardedSSSP_proposition_B_3
-- name    : GuardedSSSP.proposition_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:46.652933+00:00
-- url     : https://prove2.me/theorems/8adb0af5-a016-4598-aa89-228813de7535
-- title:
--   Proposition B.3 — active-core size charge $\sigma+k/2\le K$
-- statement:
--   Let $(G,s)$ be a finite rooted directed multigraph and delete every arc $(u,v)$ whose head $v$ dominates its tail $u$. In the remaining graph let $m_s$ be the number of arcs leaving $s$, $d_s$ the number of distinct heads among them, $\sigma=m_s-d_s$, and $k$ the number of remaining arcs whose tail is not $s$. Then
--
--   $$\sigma+\frac k2\le K_{\mathrm{CA}}(G,s).$$
--
--   The bound pays for the source-class minima and the size of the active core in the reduction of Specification 3.3.
--
--   Differences from the source:
--   - encoding: domination over source-to-u paths → domination over walks from s to u, vertices counted with both endpoints; reason: a walk avoiding v contains a simple path avoiding v; same relation
--   - encoding: K → KCA G s of the given (undeleted) graph; reason: the K of (16) and Theorem 1.1 is the benchmark of the input topology
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Proposition B.3, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist
import Definitions.Def_GuardedSSSP_KCA
import Definitions.Def_GuardedSSSP_Dominates

namespace GuardedSSSP

open AtomicDynRouting.ResidenceTime

open Classical in
/-- **Proposition B.3** (Active-core size charge), p.33 (PDF p.34).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "Delete every primitive (u, v) whose head dominates its tail. In
the remaining graph let m_s be the number of source primitives, d_s the number of their endpoint classes,
σ = m_s − d_s, and k the number of other primitives. Then σ + k/2 ≤ K."

The remaining (active) arcs are those whose head does not dominate their tail. `m_s` counts active arcs
with tail `s`, `d_s` the distinct heads among them, and `k` the active arcs with tail `≠ s`. Then
`m_s − d_s + k/2 ≤ K_CA(G, s)`, the benchmark of the original topology.

**Formalization Note.** `K` is `KCA G s` of the given graph `(G, s)`, before deletion. Loops and arcs into
`s` are inactive (a vertex dominates itself, and `s` dominates every vertex), and so are arcs leaving an
unreachable vertex. -/
theorem proposition_B_3 {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) :
    let act := Finset.univ.filter (fun e : Fin m => ¬ Dominates G s (G.head e) (G.tail e))
    let src := act.filter (fun e => G.tail e = s)
    let ms := src.card
    let ds := (src.image G.head).card
    let k := (act.filter fun e => G.tail e ≠ s).card
    (ms : ℝ) - ds + (k : ℝ) / 2 ≤ KCA G s := by sorry

end GuardedSSSP
