-- Prove2me | Theorems.Thm_GeneralizedSortingFourCycles_Sorting_claim_2
-- name    : GeneralizedSortingFourCycles.Sorting.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:50.57213+00:00
-- url     : https://prove2.me/theorems/b2443a68-0b2e-4ad5-b683-3ed9aa8af378
-- title:
--   Claim 2 — the degree-bucket sum
-- statement:
--   Let $H$ be the active simple graph on $n$ vertices, with $m$ undirected edges. Its entry degrees define the dyadic buckets $V_i=\{v:2^{i-1}<d(v)\le2^i\}$; write $B_i=2^i$ and $n_i=|V_i|$. Then
--   $$\sum_i B_i^{1/3}n_i^{2/3}\le4(nm)^{1/3}.$$
--   This is the aggregate bucket estimate used in the paper's peeling bound. Isolated vertices contribute nothing. Empty graphs, including $n=0,1$, have both sides zero.
--
--   Differences from the source:
--   - encoding: the dyadic degree buckets indexed by 0 ≤ i < 2 ln n → the actual entry-degree buckets indexed by Fin (Nat.log2 n + 2); reason: this integer range covers every positive degree; any additional source buckets are empty
--   - generalization: the standing sufficiently-large-size convention of §3 → every natural size n, including empty graphs and n=0,1; reason: the inequality also holds at the added sizes and specializes to all source instances
-- source:
--   Soheil Behnezhad, Shane Ferrante, STOC 2027 submission #1354 (October 2026), Claim 2, printed p. 13 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1354.pdf

import Mathlib
import Definitions.Def_GeneralizedSortingFourCycles_Sorting_DegreeBuckets

open scoped BigOperators

namespace GeneralizedSortingFourCycles.Sorting

/-- Claim 2, printed p. 13 (PDF p. 14), with actual dyadic entry-degree buckets.
The inequality also holds on empty graphs and at n=0 or n=1. -/
theorem claim_2 (n : ℕ) (H : SimpleGraph (Fin n)) :
    (∑ i : Fin (bucketCount n),
      (bucketUpper i.val : ℝ) ^ (1 / 3 : ℝ) *
        ((degreeBucket H i.val).card : ℝ) ^ (2 / 3 : ℝ)) ≤
      4 * ((n : ℝ) * (activeEdgeCount H : ℝ)) ^ (1 / 3 : ℝ) := by sorry

end GeneralizedSortingFourCycles.Sorting
