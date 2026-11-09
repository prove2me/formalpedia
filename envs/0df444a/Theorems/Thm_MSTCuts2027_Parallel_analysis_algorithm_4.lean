-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_analysis_algorithm_4
-- name    : MSTCuts2027.Parallel.analysis_algorithm_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:23.901004+00:00
-- url     : https://prove2.me/theorems/84d039c3-7584-4ac2-accd-8e8cab4e20a7
-- title:
--   Appendix E — Algorithm 4 achieves the depth and work of Theorem 3
-- statement:
--   There are constants $c_D,c_W$ such that for every $n$, every symmetric real cut function $F$ on $n$ vertices, every correct single-pair procedure $P$ for $F$, and all bounds $D_P,W_P$ on the depth and work of its queries: the program of Algorithm 4 halts on the initial memory, stores for every ordered pair of distinct vertices a pointer to a mincut and the mincut value, and if $n\ge2$,
--   $$\text{depth}\le c_D\bigl(\lceil\log_2 n\rceil D_P+\lceil\log_2 n\rceil^2\bigr),\qquad \text{work}\le c_W\bigl(n\lceil\log_2 n\rceil W_P+n^2\bigr).$$
--
--   This is the source's analysis of its specific algorithm, and it immediately gives Theorem 3.
--
--   Differences from the source:
--   - encoding: O(·) bounds → constants c_D, c_W fixed before the instance, for n ≥ 2, with ⌈log₂ n⌉; reason: the bounds are not meaningful for n ≤ 1, where the program still halts with a vacuously correct output
--   - encoding: Algorithm 4, including line 7 of Algorithm 2 → the program without that line, which computes a tree that no step of the cut output reads; reason: the claim concerns the cut output; omitting the step only lowers the costs
--   - encoding: DP(u, v), WP(u, v) → any common bounds DP, WP on all queries; reason: the source uses one depth and one work figure for all the pairs queried
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Analysis of Algorithm 4 (unnumbered), printed p. 25, PDF p. 27

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- The analysis of Algorithm 4 in Appendix E: the program `algorithms`, started at `pMain` on the
initial memory, outputs all-pairs mincuts within the depth and work of Theorem 3. -/
theorem analysis_algorithm_4 :
    ∃ cD cW : ℕ, ∀ (n : ℕ) (F : Finset (Fin n) → ℝ), IsSymmetricCutFunction F →
      ∀ P : Oracle ℝ n, IsMincutOracle F P →
      ∀ DP WP : ℕ, (∀ u v : Fin n, u ≠ v → (P u v).depth ≤ DP ∧ (P u v).work ≤ WP) →
        ∃ o : Outcome ℝ,
          Halts (machine P) algorithms Prog.pMain [] (initialStore ℝ n) o ∧
          AllPairsOutput F o.store ∧
          (2 ≤ n →
            o.depth ≤ cD * (Nat.clog 2 n * DP + (Nat.clog 2 n) ^ 2) ∧
            o.work ≤ cW * (n * Nat.clog 2 n * WP + n ^ 2)) := by sorry

end MSTCuts2027.Parallel
