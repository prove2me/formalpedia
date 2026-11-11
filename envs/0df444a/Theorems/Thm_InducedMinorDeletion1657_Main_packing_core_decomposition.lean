-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_packing_core_decomposition
-- name    : InducedMinorDeletion1657.Main.packing_core_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:54.107076+00:00
-- url     : https://prove2.me/theorems/37287870-45e5-44ab-94b1-28eb1feeb07e
-- title:
--   Corollary 3.6 — packing and core decomposition
-- statement:
--   Given $G$, a treewidth-$t$ modulator $M$, and positive integers $d,t$, compute a collection $(V_i,Z_i)$ in time $C2^{Ct}(n+1)^c$, with uniform constants. All $V_i,Z_i$ lie outside $M$ and satisfy:
--   1. The sets $V_i$ are pairwise disjoint and $Z_i\subseteq V_i$.
--   2. Each $G[V_i]$ is connected and $|N_G(V_i)\cap M|>d$.
--   3. $|Z_i|\le Ct$ for every $i$.
--   4. $M$ is a $d$-core of $G-\bigcup_iZ_i$.
--
--   The collection may be empty. This decomposes the failure of $M$ to be a core and retains every source clause.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite published register program, actual halting iteration, output charge and logarithmically bounded words; reason: operational word-RAM reading; constants and the program precede every varying graph and numerical input
--   - encoding: O notation and small input bases n, k → positive uniform constants, n+1 and k+2, and an upper bound on collection size; reason: makes source asymptotics pointwise at small inputs without changing any unbounded parameter dependence
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 13 (PDF p. 14), Corollary 3.6

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Corollary 3.6, printed p. 13 / PDF p. 14. See the local source audit for conventions. -/
theorem packing_core_decomposition :
∃ (P : Program) (C c q : ℕ), 0 < C ∧ 0 < c ∧ 0 < q ∧
  ∀ (G : InputGraph) (M : Finset (Fin G.n)) (d t : ℕ),
    0 < d → 0 < t → modulator G.graph t M →
    ∃ L : List (Finset (Fin G.n) × Finset (Fin G.n)),
      packingResult G M d t C L ∧
      ramOutputs P (d :: t :: (graphWords G ++ subsetWords M)) (pairWords L)
        (polyTime C c G.n * (2 : ℝ) ^ (C * (t : ℝ))) q := by sorry

end InducedMinorDeletion1657.Main
