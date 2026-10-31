-- Prove2me | Theorems.Thm_MehtaOnlineAdAllocation_MSVV_eq_5_2
-- name    : MehtaOnlineAdAllocation.MSVV.eq_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:37:59.840163+00:00
-- url     : https://prove2.me/theorems/6ff93ef7-625d-4f1a-86de-533002d7d63a
-- title:
--   Equation (5.2) — slab/type relation
-- statement:
--   For a finite vector of actual unit-budget terminal spends $0\le s_u\le1$, a positive integer $k$ and $1\le i\le k$, the source claims
--   $$\beta_i=\frac{N-\sum_{1\le j<i}\alpha_j}{k}.$$
--   Here $\alpha$ counts types and $\beta$ measures physical slab volume. No exact filling of terminal slabs is assumed. This is the literal source equality; the partial-slab discrepancy is recorded in finding I1.
--
--   Differences from the source:
--   - generalization: the final unit-budget spend vector of the algorithm → every finite vector with entries in [0,1]; reason: the displayed assertion is presented as geometric, and every source terminal vector is an instance
--   - reading: type i has spend between (i-1)/k and i/k → the interval ((i-1)/k,i/k], with zero assigned to type 1; reason: the source does not settle endpoints, and this gives a disjoint partition without changing actual spend
--   - generalization: a large positive integer discretization constant k → every integer k at least 1; reason: all source choices of k remain included
--   - encoding: the finite set U of advertisers → Fin N with real-valued counts and subtraction; reason: enumeration preserves all finite spend vectors, and real subtraction is the displayed arithmetic
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), §5.2, equation (5.2), printed p. 312 (PDF p. 50).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_alpha
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_beta

namespace MehtaOnlineAdAllocation.MSVV

theorem eq_5_2 {N : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (s : Fin N → ℝ) (hs : ∀ u, 0 ≤ s u ∧ s u ≤ 1)
    (i : ℕ) (hi : 1 ≤ i ∧ i ≤ k) :
    beta k s i = ((N : ℝ) - ∑ j ∈ Finset.Ico 1 i, alpha k s j) / (k : ℝ) := by sorry

end MehtaOnlineAdAllocation.MSVV
