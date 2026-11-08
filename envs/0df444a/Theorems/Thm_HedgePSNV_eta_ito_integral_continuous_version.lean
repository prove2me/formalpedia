-- Prove2me | Theorems.Thm_HedgePSNV_eta_ito_integral_continuous_version
-- name    : HedgePSNV.eta_ito_integral_continuous_version
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T14:52:24.600666+00:00
-- url     : https://prove2.me/theorems/00f5c6e6-8e12-444f-976e-9414bb475a5d
-- title:
--   Continuous adapted version of $I=\int\eta\,dB$
-- statement:
--   Given continuous versions of bounded continuous Itô integrals, there is a continuous adapted $I$ with $I_0=0$, $$I=\int_0^\cdot\eta_{s\wedge T}\,dB_s,\qquad I_t=\mathcal I_t\ \text{a.s. for }t\le T,$$ where $\mathcal I$ is the model's integral.
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes).
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Chapter 3, Section 3.2.B (continuous modification of the stochastic integral); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem eta_ito_integral_continuous_version {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) (W : ℝ≥0 → Ω → SDEState 2)
    (hW : ∀ t ω, W t ω = WithLp.toLp 2
      ![if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.B t ω,
        if ω ∈ toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}
          then 0 else M.Bt t ω])
    (hC : ∀ H : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable[completedBrownianPast M.P W (fun _ => 0) s] (H s)) →
      (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
      ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
        (∀ t, Measurable[completedBrownianPast M.P W (fun _ => 0) t] (Jc t)) ∧
        (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
        HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
          (fun s ω => W s ω 0) H Jc) :
    ∃ Ic : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Ic t ω) ∧
      (∀ t, Measurable[completedBrownianPast M.P W (fun _ => 0) t] (Ic t)) ∧
      (∀ t, Measurable (Ic t)) ∧ (∀ ω, Ic 0 ω = 0) ∧
      HasBrownianItoIntegral M.P (completedBrownianPast M.P W (fun _ => 0))
        (fun s ω => W s ω 0) (fun s ω => M.η (min s p.T) ω) Ic ∧
      (∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) := by sorry

end HedgePSNV
