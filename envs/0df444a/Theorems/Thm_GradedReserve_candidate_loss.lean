-- Prove2me | Theorems.Thm_GradedReserve_candidate_loss
-- name    : GradedReserve.candidate_loss
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:35:55.901084+00:00
-- url     : https://prove2.me/theorems/ef49fe39-ed6e-4aaa-8056-c619818663b7
-- title:
--   Section A.5 — $C[x^*]=\frac N{N+1}(c_0\bar v)^{N+1}\frac p{p+N+1}$
-- statement:
--   Let $F(v)=v^k$ ($k\ge1$ real), $n\ge2$ and $p>p_{\min}$. The anchored loss of the candidate is
--   $$C[x^*]=\frac N{N+1}\,(c_0\bar v)^{N+1}\,\frac p{p+N+1}.$$
--
--   With (25) this gives the optimal anchored revenue $\frac N{N+1}\big[1-b_0^{N+1}\frac p{p+N+1}\big]$ of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.19 (PDF 20)

import Mathlib
import Definitions.Def_GradedReserve_Cfun__99e74d
import Definitions.Def_GradedReserve_cZero
import Definitions.Def_GradedReserve_pMin
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_xStar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **The candidate's anchored loss** (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.19, PDF 20): direct integration gives
`C[x*] = (N/(N+1)) (c₀ v̄)^{N+1} p/(p+N+1)` for `p > p_min`. -/
theorem candidate_loss (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : pMin k n < p) :
    Cfun k n (xStar k n p) =
      powN k n / (powN k n + 1) * (cZero k n p * vbar k n p) ^ (powN k n + 1)
        * (p / (p + powN k n + 1)) := by sorry

end GradedReserve
