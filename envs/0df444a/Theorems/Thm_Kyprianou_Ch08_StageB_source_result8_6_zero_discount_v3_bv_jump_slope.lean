-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv_jump_slope
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_jump_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:21:09.305347+00:00
-- url     : https://prove2.me/theorems/f1988922-e7a5-4bb7-8381-4ad4d11d0baf
-- title:
--   Bounded-variation compensated jump quotient limit
-- statement:
--   Under bounded variation, the compensated negative-jump Levy integral divided by the large positive parameter tends to minus the finite first moment of jumps in (-1,0); small jumps use the finite first absolute moment and large jumps use Levy quadratic integrability.
-- source:
--   Lemma 8.6 corrected proof: dominated convergence split over Ioo (-1,0) and Iic (-1) for the bounded-variation bracket.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_jump_slope :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ =>
        (∫ x, (Real.exp (β * x) - 1 - (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β)
        atTop (𝓝 (-∫ x in Set.Ioo (-1 : ℝ) 0, x ∂D.triplet.levyMeasure)) := by sorry
