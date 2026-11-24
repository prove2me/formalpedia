-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_interval_occupation_qpos_set_identity
-- name    : Kyprianou.Ch08.StageB.p2m87_interval_occupation_qpos_set_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:16:21.238138+00:00
-- url     : https://prove2.me/theorems/1f71b175-0746-459f-a474-7a83c0a7ca17
-- title:
--   8.7 occupation identity, positive discount
-- statement:
--   Measurable-set killed occupation density in the strictly positive discount regime q>0, with full original stochastic model assumptions.
-- source:
--   Kyprianou (2006), Chapter 8, source results 8.7–8.9.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- 8.7: killed two-sided occupation identity on measurable sets. -/
theorem p2m87_interval_occupation_qpos_set_identity :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
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
