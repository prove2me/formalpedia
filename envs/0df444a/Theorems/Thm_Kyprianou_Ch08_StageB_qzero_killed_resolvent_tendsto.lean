-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_resolvent_tendsto
-- name    : Kyprianou.Ch08.StageB.qzero_killed_resolvent_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:01:10.342903+00:00
-- url     : https://prove2.me/theorems/21dded5b-7045-4c1b-9bdb-564c14601851
-- title:
--   Zero-discount convergence of the killed interval resolvent
-- statement:
--   Along the reciprocal positive discounts, the discounted two-sided killed occupation resolvent increases to its undiscounted value on every measurable set. This is the stochastic-side limit of the zero-discount occupation identity.
-- source:
--   Kyprianou (2006), Chapter 8, monotone convergence of the killed occupation resolvent as discount tends to zero.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open scoped Topology

namespace Kyprianou.Ch08.StageB

/-- Resolvent-side sequential limit for the zero-discount occupation identity. -/
theorem qzero_killed_resolvent_tendsto :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        Tendsto
          (fun n : ℕ =>
            ∫⁻ t : ℝ≥0,
              ENNReal.ofReal
                (Real.exp (-(((n : ℝ) + 1)⁻¹) * (t : ℝ))) *
                P {ω | (t : WithTop ℝ≥0) <
                  min (tauMinus (shifted D.X x) 0 ω)
                    (tauPlus (shifted D.X x) a ω) ∧
                  shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)
          atTop
          (𝓝 (∫⁻ t : ℝ≥0,
            P {ω | (t : WithTop ℝ≥0) <
              min (tauMinus (shifted D.X x) 0 ω)
                (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)) := by
  sorry

end Kyprianou.Ch08.StageB
