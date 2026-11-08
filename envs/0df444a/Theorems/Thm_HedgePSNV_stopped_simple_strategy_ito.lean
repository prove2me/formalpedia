-- Prove2me | Theorems.Thm_HedgePSNV_stopped_simple_strategy_ito
-- name    : HedgePSNV.stopped_simple_strategy_ito
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:30:45.869561+00:00
-- url     : https://prove2.me/theorems/580e16b4-8ad5-4511-ab5e-1df99ff79e32
-- title:
--   A stopped one-step strategy has the Itô integral $Y(J_{s'\wedge\tau}-J_{s\wedge\tau})$
-- statement:
--   For $s\le s'<T$, a stopping time $\tau$ and a bounded $\mathcal F_s$-measurable $Y$, $$\int_0^t \mathbf 1_{\{s\wedge\tau\le u<s'\wedge\tau\}}Y\,X_u\sigma_u\,dB_u=Y\big(J_{s'\wedge\tau\wedge t}-J_{s\wedge\tau\wedge t}\big).$$
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes).
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.2, Proposition 2.10 (stochastic integral of simple processes) and Ch. 3 (2.19); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped NNReal

namespace HedgePSNV

theorem stopped_simple_strategy_ito {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (s s' : ℝ≥0)
    (hss : s ≤ s') (hs' : s' < p.T)
    (τ : Ω → ℝ≥0) (hτ : ∀ u, MeasurableSet[M.F u] {ω | τ ω ≤ u}) (Y : Ω → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hYb : ∀ ω, |Y ω| ≤ C) (hYm : StronglyMeasurable[M.F s] Y) :
    HasBrownianItoIntegral M.P (fun t => M.F t) M.B
      (fun u ω => (if min s (τ ω) ≤ u ∧ u < min s' (τ ω) then Y ω else 0) * (M.X u ω * M.σ u ω))
      (fun t ω => Y ω * (M.J (min (min s' (τ ω)) t) ω - M.J (min (min s (τ ω)) t) ω)) := by sorry

end HedgePSNV
