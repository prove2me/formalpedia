-- Prove2me | Theorems.Thm_GeneralizedSortingFourCycles_Sorting_claim_1
-- name    : GeneralizedSortingFourCycles.Sorting.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:50.010772+00:00
-- url     : https://prove2.me/theorems/03753610-597d-451d-88b3-80ec04fea40e
-- title:
--   Claim 1 — bipartite four-cycle supersaturation
-- statement:
--   Let $a,b\ge2$ be integers and let $G\subseteq K_{a,b}$ be a simple bipartite graph with $m$ edges. If
--   $$m\ge2(a\sqrt b+b\sqrt a),$$
--   then the number $C_4(G)$ of distinct unordered four-cycles satisfies
--   $$C_4(G)\ge\frac{m^4}{32a^2b^2}.$$
--   The inequality controls cycle abundance from edge density, with the paper's exact constant and both parts of its density threshold.
--
--   Differences from the source:
--   - encoding: a bipartite subgraph of K_{a,b} and its distinct four-cycles → a finite edge subset of Fin a × Fin b and increasing vertex pairs on both sides; reason: finite relabeling preserves all instances and counts every unordered cycle once
-- source:
--   Soheil Behnezhad, Shane Ferrante, STOC 2027 submission #1354 (October 2026), Claim 1, printed p. 11 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1354.pdf

import Mathlib
import Definitions.Def_GeneralizedSortingFourCycles_Sorting_CycleModel

namespace GeneralizedSortingFourCycles.Sorting

/-- Claim 1, printed p. 11 (PDF p. 12): the denominator is exactly 32,
and the count uses unordered pairs on each side, with no multiplicity. -/
theorem claim_1 (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (E : Finset (Fin a × Fin b))
    (hm : 2 * ((a : ℝ) * Real.sqrt b + (b : ℝ) * Real.sqrt a) ≤ (E.card : ℝ)) :
    (E.card : ℝ) ^ 4 / (32 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2) ≤
      ((fourCycles E).card : ℝ) := by sorry

end GeneralizedSortingFourCycles.Sorting
