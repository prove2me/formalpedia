-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_exponent_slope_from_jump_limit
-- name    : Kyprianou.Ch08.StageB.p2m86_bv_exponent_slope_from_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:54:40.799997+00:00
-- url     : https://prove2.me/theorems/de453a41-3e07-4d75-8d66-6cadf8be0413
-- title:
--   8.6: exponent slope from compensated jump slope and triplet identity
-- statement:
--   Under the original Lévy model, source Laplace-exponent equality and BV triplet hypothesis, the compensated jump-quotient limit implies the Laplace-exponent slope equals positive-variation physical drift. Contains no new assumptions beyond the source hypotheses and the separately proved jump limit.
-- source:
--   Kyprianou (2006), Lemma 8.6, corrected triplet exponent-to-physical drift identity.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Identify the Laplace-exponent BV slope using the exact compensated jump limit. -/
theorem p2m86_bv_exponent_slope_from_jump_limit :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ =>
        (∫ x, (Real.exp (β * x) - 1 -
          (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β)
        atTop (𝓝 (-∫ x in Set.Ioo (-1 : ℝ) 0, x ∂D.triplet.levyMeasure)) →
      Tendsto (fun β : ℝ => ψ β / β) atTop
        (𝓝 (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)) := by
  sorry

end Kyprianou.Ch08.StageB
