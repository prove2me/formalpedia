-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_compensated_integral_exact_partition
-- name    : Kyprianou.Ch08.StageB.p2m86_bv_compensated_integral_exact_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:53:53.143589+00:00
-- url     : https://prove2.me/theorems/79478cec-7c60-45fb-8ea8-1712901d467d
-- title:
--   8.6 bounded-variation exact compensated integral partition
-- statement:
--   For positive Laplace argument, split the compensated negative-jump integral into the small-jump interval (-1,0) and the large-jump interval (-∞,-1], using zero Lévy measure on [0,∞), without changing the original source model.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.6 corrected branch, integral split.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Exact full compensated jump quotient as small and large jump integrals. -/
theorem p2m86_bv_compensated_integral_exact_partition :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      ∀ β : ℝ, 0 < β →
      (∫ x, (Real.exp (β * x) - 1 -
        (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β =
      (∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) +
      (∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure) := by
  sorry

end Kyprianou.Ch08.StageB
