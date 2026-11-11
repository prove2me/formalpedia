-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_closure
-- name    : InducedMinorDeletion1657.Main.closure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:43.550731+00:00
-- url     : https://prove2.me/theorems/03c27e3d-6008-4ad3-9181-b0c5a1c9062b
-- title:
--   Lemma 3.7 — closure (corrected: width-zero size bound)
-- statement:
--   For any finite graph $G$ and prescribed vertex set $Z$, put $w=\operatorname{tw}(G)$. A uniform algorithm computes $L\supseteq Z$ such that
--   $$L\text{ is an }8w\text{-core},\quad |L|\le8\max(1,w)|Z|,\quad T\le C2^{Cw}(n+1)^c.$$
--   No decomposition is supplied and neither $Z\ne\varnothing$ nor $w>0$ is assumed. The numerical factor eight follows from the proof's width-$W\le2w+1$ decomposition and $2(W+1)\le8w$ for $w\ge1$. At width zero one can take $L=Z$, a zero-core. This is the closure interface used by core branching.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite published register program, actual halting iteration, output charge and logarithmically bounded words; reason: operational word-RAM reading; constants and the program precede every varying graph and numerical input
--   - encoding: O notation and small input bases n, k → positive uniform constants, n+1 and k+2, and an upper bound on collection size; reason: makes source asymptotics pointwise at small inputs without changing any unbounded parameter dependence
--   - correction: |L|=O(w|Z|) including w=0 → |L|≤8 max(1,w)|Z| and core order 8w; reason: the one-vertex edgeless graph with Z=V(G) has w=0 but |L|≥1; the proof itself has +1 factors and yields the stated factor eight at positive width
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 14 (PDF p. 15), Lemma 3.7

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 3.7, printed p. 14 / PDF p. 15. See the local source audit for conventions. -/
theorem closure :
∃ (P : Program) (C c q : ℕ), 0 < C ∧ 0 < c ∧ 0 < q ∧
  ∀ (G : InputGraph) (Z : Finset (Fin G.n)),
    ∃ L : Finset (Fin G.n), Z ⊆ L ∧ core G.graph L (8 * width G.graph) ∧
      L.card ≤ 8 * max 1 (width G.graph) * Z.card ∧
      ramOutputs P (graphWords G ++ subsetWords Z) (subsetWords L)
        (polyTime C c G.n * (2 : ℝ) ^ (C * (width G.graph : ℝ))) q := by sorry

end InducedMinorDeletion1657.Main
