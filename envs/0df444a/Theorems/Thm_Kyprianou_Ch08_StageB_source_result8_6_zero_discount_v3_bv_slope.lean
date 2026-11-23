-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv_slope
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_slope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:21:09.508945+00:00
-- url     : https://prove2.me/theorems/9c5ecb61-4003-4b98-96d4-4777c77c1c3e
-- title:
--   Bounded-variation exponent slope identifies physical drift
-- statement:
--   For a bounded-variation source model, the large-frequency quotient of the Laplace exponent tends to the physical drift obtained from the characteristic drift -D.triplet.drift and the finite small-jump first moment.
-- source:
--   Lemma 8.6 corrected proof: positive-mgf triplet identification plus the bounded-variation compensated jump quotient limit.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_slope :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ => ψ β / β) atTop
        (𝓝 (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)) := by sorry
