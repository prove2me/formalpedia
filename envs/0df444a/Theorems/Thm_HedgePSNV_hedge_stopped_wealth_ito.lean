-- Prove2me | Theorems.Thm_HedgePSNV_hedge_stopped_wealth_ito
-- name    : HedgePSNV.hedge_stopped_wealth_ito
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:25:23.738604+00:00
-- url     : https://prove2.me/theorems/779d6357-5365-4a69-96a1-1034a5c47340
-- title:
--   The stopped wealth process is an Itô integral of $X\sigma$
-- statement:
--   For the canonical 2-dimensional Brownian motion $W=(B,\tilde B)$ (set to 0 on the null set of discontinuous paths), $$J_{T\wedge t}-J_0+X_T\sigma_T(B_t-B_{T\wedge t})=\int_0^t X_{s\wedge T}\sigma_{s\wedge T}\,dB_s$$ in the sense of `HasBrownianItoIntegral` with respect to the completed Brownian filtration.
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes).
-- source:
--   Wang-Yao-Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, https://arxiv.org/abs/2201.01026v4, Section 3.1, (2) (asset dynamics); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped NNReal
open Classical

namespace HedgePSNV

theorem hedge_stopped_wealth_ito {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (W : ℝ≥0 → Ω → SDEState 2)
    (hW : ∀ t ω, W t ω = WithLp.toLp 2
      ![if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.B t ω,
        if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.Bt t ω]) :
    HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
      (fun s ω => W s ω 0) (fun s ω => M.X (min s p.T) ω * M.σ (min s p.T) ω)
      (fun t ω => (M.J (min p.T t) ω - M.J 0 ω) +
        M.X p.T ω * M.σ p.T ω * (M.B t ω - M.B (min p.T t) ω)) := by sorry

end HedgePSNV
