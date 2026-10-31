-- Prove2me | Theorems.Thm_MehtaOnlineAdAllocation_MSVV_eq_5_8
-- name    : MehtaOnlineAdAllocation.MSVV.eq_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:39:20.779426+00:00
-- url     : https://prove2.me/theorems/dbe9b276-fc3d-423c-aa8e-2ef79e59b997
-- title:
--   Equation (5.8) — aggregate weighted comparison
-- statement:
--   Fix a unit-budget instance, $k\ge1$, bids at most $1/k^2$, a raw-bid proof run $\sigma$, and an offline allocation $\tau$ that spends every bidder’s entire unit budget. With types and physical slab volumes computed from $\sigma$’s actual capped terminal spends, the printed assertion is
--   $$\sum_{i=1}^k\psi(i/k)\alpha_i\le\sum_{i=1}^k\psi(i/k)\beta_i.$$
--   No weighted inequality or slab identity is assumed. Full spending of the offline allocation is the proof-local simplifying assumption; it is absent from the main performance theorem. The difference between query weights and physical slab weights is recorded in finding I2.
--
--   Differences from the source:
--   - generalization: bids much smaller than 1/k², with the Balance warm-up explicitly using at most 1/k² → all bids at most 1/k² in the unit-budget proof model; reason: this includes every sufficiently small source instance without inserting an arbitrary smaller cutoff
--   - reading: type i has spend between (i-1)/k and i/k → the interval ((i-1)/k,i/k], with zero assigned to type 1; reason: the source does not settle endpoints, and this gives a disjoint partition without changing actual spend
--   - generalization: a large positive integer discretization constant k → every integer k at least 1; reason: all source choices of k remain included
--   - encoding: finite advertisers and query occurrences → Fin N and Fin M with an Option-valued allocation; reason: enumeration preserves every finite instance and arrival order
--   - encoding: OPT spends the entire budget of every bidder → an allocation tau with capped terminal spend 1 for every bidder; reason: such an allocation attains the sum-of-budgets upper bound and is therefore an optimum
--   - encoding: the proof ignores capping in bid comparisons but depicts capped terminal spend → IsRawRun supplies the trajectory, and capped spend supplies alpha and beta; reason: the source distinguishes these roles on pp. 308 and 312
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), §5.2, equation (5.8), printed p. 315 (PDF p. 53); standing proof assumptions, pp. 312–313 (PDF pp. 50–51).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_IsRawRun
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_SmallBids
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_alpha
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_beta

namespace MehtaOnlineAdAllocation.MSVV

theorem eq_5_8 {N M : ℕ} (I : Instance N M)
    (hunit : ∀ u, I.budget u = 1) (k : ℕ) (hk : 1 ≤ k)
    (hsmall : SmallBids I (1 / (k : ℝ) ^ 2))
    (σ : Allocation N M) (hσ : IsRawRun I σ)
    (τ : Allocation N M) (hfull : ∀ u, spend I τ u M = 1) :
    (∑ i ∈ Finset.Icc 1 k,
      psi ((i : ℝ) / (k : ℝ)) * alpha k (fun u => spend I σ u M) i) ≤
    ∑ i ∈ Finset.Icc 1 k,
      psi ((i : ℝ) / (k : ℝ)) * beta k (fun u => spend I σ u M) i := by sorry

end MehtaOnlineAdAllocation.MSVV
