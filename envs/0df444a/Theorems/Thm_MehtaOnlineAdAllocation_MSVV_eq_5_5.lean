-- Prove2me | Theorems.Thm_MehtaOnlineAdAllocation_MSVV_eq_5_5
-- name    : MehtaOnlineAdAllocation.MSVV.eq_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:37:48.64574+00:00
-- url     : https://prove2.me/theorems/60338adc-f7ed-4e15-835e-f03e9f1f80d7
-- title:
--   Equation (5.5) — actual spend in terms of types
-- statement:
--   For a finite vector of actual unit-budget terminal spends $0\le s_u\le1$ and a positive integer $k$, the source claims
--   $$\sum_u s_u=\sum_{i=1}^k\frac{i}{k}\alpha_i.$$
--   The left side is actual revenue, not rounded revenue. The partial-slab discrepancy is retained and documented as I1.
--
--   Differences from the source:
--   - generalization: the final unit-budget spend vector of the algorithm → every finite vector with entries in [0,1]; reason: the displayed assertion is presented as geometric, and every source terminal vector is an instance
--   - reading: type i has spend between (i-1)/k and i/k → the interval ((i-1)/k,i/k], with zero assigned to type 1; reason: the source does not settle endpoints, and this gives a disjoint partition without changing actual spend
--   - generalization: a large positive integer discretization constant k → every integer k at least 1; reason: all source choices of k remain included
--   - encoding: the finite set U of advertisers → Fin N and real-valued type counts; reason: enumeration changes no spend vector or sum
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), §5.2, equation (5.5), printed p. 314 (PDF p. 52), reused in the general argument on printed p. 315 (PDF p. 53).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_alpha

namespace MehtaOnlineAdAllocation.MSVV

theorem eq_5_5 {N : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (s : Fin N → ℝ) (hs : ∀ u, 0 ≤ s u ∧ s u ≤ 1) :
    (∑ u, s u) = ∑ i ∈ Finset.Icc 1 k, (i : ℝ) / (k : ℝ) * alpha k s i := by sorry

end MehtaOnlineAdAllocation.MSVV
