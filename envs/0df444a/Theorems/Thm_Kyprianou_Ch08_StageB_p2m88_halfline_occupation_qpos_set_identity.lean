-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_halfline_occupation_qpos_set_identity
-- name    : Kyprianou.Ch08.StageB.p2m88_halfline_occupation_qpos_set_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T21:13:56.858937+00:00
-- url     : https://prove2.me/theorems/b0b7457b-9e60-43a0-987c-b643656f3862
-- title:
--   8.8 occupation identity, positive discount
-- statement:
--   Measurable-set killed occupation density in the strictly positive discount regime q>0, with full original stochastic model assumptions.
-- source:
--   Kyprianou (2006), Chapter 8, source results 8.7–8.9.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- 8.8: killed half-line occupation identity on measurable sets. -/
theorem p2m88_halfline_occupation_qpos_set_identity :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), 0 < q → 0 ≤ x →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Ici 0)).withDensity
      (fun y : ℝ => ENNReal.ofReal
        (killedHalflineDensity ψ q (W q) x y))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            tauMinus (shifted D.X x) 0 ω ∧
            shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  sorry

end Kyprianou.Ch08.StageB
