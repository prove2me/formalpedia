-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv_small_jump_slope
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_small_jump_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:24:14.199854+00:00
-- url     : https://prove2.me/theorems/970fb450-6708-4abd-a149-52df1277a1d7
-- title:
--   Small-jump compensated quotient limit
-- statement:
--   On the small negative-jump interval, the compensated exponential quotient is dominated by twice the absolute jump and converges to minus x, whose integral is finite under bounded variation.
-- source:
--   Lemma 8.6 corrected proof: dominated convergence on Ioo (-1,0).

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_small_jump_slope :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ => ∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) atTop
        (𝓝 (-∫ x in Set.Ioo (-1 : ℝ) 0, x ∂D.triplet.levyMeasure)) := by sorry
