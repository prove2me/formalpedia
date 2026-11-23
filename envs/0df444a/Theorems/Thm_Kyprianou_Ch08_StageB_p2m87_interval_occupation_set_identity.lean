-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_interval_occupation_set_identity
-- name    : Kyprianou.Ch08.StageB.p2m87_interval_occupation_set_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:57:58.892802+00:00
-- url     : https://prove2.me/theorems/726c937e-d573-430f-8b8a-e5b9ae86f0d1
-- title:
--   8.7: killed two-sided occupation identity on measurable sets
-- statement:
--   Core finite-interval resolvent density identity on all measurable test sets. Build from stopped occupation and the two-sided exit identities; the parent then reconstructs the measure.
-- source:
--   Kyprianou (2006), Chapter 8, source results 8.7–8.9.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- 8.7: killed two-sided occupation identity on measurable sets. -/
theorem p2m87_interval_occupation_set_identity :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Icc 0 a)).withDensity
      (fun y : ℝ => ENNReal.ofReal (killedIntervalDensity (W q) a x y))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            min (tauMinus (shifted D.X x) 0 ω)
              (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  sorry

end Kyprianou.Ch08.StageB
