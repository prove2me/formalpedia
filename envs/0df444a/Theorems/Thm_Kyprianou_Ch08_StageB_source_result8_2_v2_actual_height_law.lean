-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_actual_height_law
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_actual_height_law
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T16:43:11.788483+00:00
-- url     : https://prove2.me/theorems/3eded364-8075-43f9-bae4-12db613bec33
-- title:
--   Theorem 8.2 source child: actual q-excursion-height law
-- statement:
--   Under the exact hypotheses of Theorem 8.2, for every nonnegative q there exists a measure n on real excursion heights satisfying the actual q-excursion-height law. The law includes PhiIsLargestRoot, finiteness of every closed tail n([h,∞)) for h>0, and the exponential identity for the original-path event NoDrawdownBeforeUpcrossing D.X a h with its exact discounted first-upcrossing payoff.
-- source:
--   Source-faithful child extracted from the first existential conjunct of Kyprianou Chapter 8, Theorem 8.2, exact original 2006 edition SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf; exact source definition sourceCertificate_result8_2 in Definitions.Def_Kyprianou_Ch08_StageCFoundation_D.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_actual_height_law
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ n : Measure ℝ, HasActualQExcursionHeightLaw P D ψ q n := by
  sorry
