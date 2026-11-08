-- Prove2me | Theorems.Thm_HedgePSNV_girsanov_density_ito
-- name    : HedgePSNV.girsanov_density_ito
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T14:57:11.714947+00:00
-- url     : https://prove2.me/theorems/5abc252f-df32-4475-98ab-f0d8e100233d
-- title:
--   The Girsanov density $Z=\exp(-I-\tfrac12\int\eta^2)$ solves $dZ=-Z\eta\,dB$
-- statement:
--   If $I=\int_0^\cdot\eta_{s\wedge T}\,dB_s$ is a continuous adapted version, then $Z_t=\exp(-I_t-\tfrac12\int_0^t\eta^2)$ satisfies $$Z_t=1+\int_0^t(-Z_s\eta_{s\wedge T})\,dB_s\quad\text{a.s. for every }t.$$
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes).
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.5, (5.2)-(5.4) (the exponential martingale) and Theorem 3.3.6 (Ito's rule); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem girsanov_density_ito {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) (W : ℝ≥0 → Ω → SDEState 2)
    (hW : ∀ t ω, W t ω = WithLp.toLp 2
      ![if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.B t ω,
        if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.Bt t ω]) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P W (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIi : HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
      (fun s ω => W s ω 0) (fun s ω => M.η (min s p.T) ω) Ic) :
    ∃ K : ℝ≥0 → Ω → ℝ,
      HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
        (fun s ω => W s ω 0) (fun s ω => -(Real.exp (-(Ic s ω) - (1 / 2) * ∫ u in (0 : ℝ)..(s).val, M.η (min u.toNNReal p.T) ω ^ 2) * M.η (min s p.T) ω)) K ∧
      ∀ t, ∀ᵐ ω ∂M.P, Real.exp (-(Ic t ω) - (1 / 2) * ∫ u in (0 : ℝ)..(t).val, M.η (min u.toNNReal p.T) ω ^ 2) = 1 + K t ω := by sorry

end HedgePSNV
