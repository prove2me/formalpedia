-- Prove2me | Theorems.Thm_MehtaOnlineAdAllocation_MSVV_eq_5_7
-- name    : MehtaOnlineAdAllocation.MSVV.eq_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:39:17.17615+00:00
-- url     : https://prove2.me/theorems/4d89be13-e980-4c59-ba3e-1d53cfbef6d3
-- title:
--   Equation (5.7) — per-query scaled-bid comparison
-- statement:
--   Fix a unit-budget instance, $k\ge1$, a run $\sigma$ of the raw-bid proof rule, a query $t$, and an advertiser $u$. If $i$ is the final type of $u$, then
--   $$b_{ut}\psi(i/k)\le \mathrm{gainedRawScore}_\sigma(t).$$
--   If $t$ is assigned to $u'$, the right side is $b_{u't}\psi(S_{u'}(t))$, exactly the source’s $b_{u'v}\psi(j/k)$ with $j=kS_{u'}(t)$. If no advertiser wins, it is zero. In particular this applies to the advertiser selected by any fixed optimum. Terminal type $k$ is included; $\psi(1)=0$. Pre-arrival spends are arbitrary real values, not grid points.
--
--   Differences from the source:
--   - generalization: the bidder u* selected by a fixed optimum under the small-bids convention → every bidder and all nonnegative real bids; reason: the local comparison uses only score maximization and decreasing psi, and includes every source comparison
--   - reading: type i has spend between (i-1)/k and i/k → the interval ((i-1)/k,i/k], with zero assigned to type 1; reason: the source does not settle endpoints, and this gives a disjoint partition without changing actual spend
--   - generalization: a large positive integer discretization constant k → every integer k at least 1; reason: all source choices of k remain included
--   - encoding: finite advertisers and query occurrences → Fin N and Fin M with an Option-valued allocation; reason: enumeration preserves every finite instance and arrival order
--   - encoding: j/k denotes the winner’s real pre-arrival spend → the actual prefix spend, with gained score zero on rejection; reason: j is real in [0,k], and zero-score rejection extends the formula to source arrivals with no available bidder
--   - encoding: the proof ignores capping in its bid comparisons → IsRawRun is separate from the capped main algorithm; reason: this keeps the source proof simplification explicit without changing the goal
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), §5.2, equations (5.6)–(5.7), printed pp. 314–315 (PDF pp. 52–53); raw-bid simplification, p. 308 (PDF p. 46).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_IsRawRun
import Definitions.Def_AdWordsMSVV_Tradeoff_Setting

namespace MehtaOnlineAdAllocation.MSVV

theorem eq_5_7 {N M : ℕ} (I : Instance N M)
    (hunit : ∀ u, I.budget u = 1) (k : ℕ) (hk : 1 ≤ k)
    (σ : Allocation N M) (hσ : IsRawRun I σ) (t : Fin M) (u : Fin N) :
    I.bid u t * psi ((AdWordsMSVV.Tradeoff.slabOf k (spend I σ u M) : ℝ) / (k : ℝ)) ≤
      gainedRawScore I σ t := by sorry

end MehtaOnlineAdAllocation.MSVV
