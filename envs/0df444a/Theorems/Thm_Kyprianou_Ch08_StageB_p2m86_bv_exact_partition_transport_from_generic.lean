-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_exact_partition_transport_from_generic
-- name    : Kyprianou.Ch08.StageB.p2m86_bv_exact_partition_transport_from_generic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:03:19.543793+00:00
-- url     : https://prove2.me/theorems/a00a11b0-cf3e-4926-ac66-252cf2df14c8
-- title:
--   8.6 BV transport for generic negative-jump split
-- statement:
--   Transport the existing negative-halfline integral partition to the target full-space quotient using the negative-jump support, quotient algebra and BV integrability.
-- source:
--   Kyprianou (2006), Lemma 8.6; reuse existing published generic negative jump partition.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Transport the existing negative-halfline integral partition to the target full-space quotient using the negative-jump support, quotient algebra and BV integrability. -/
theorem p2m86_bv_exact_partition_transport_from_generic :
    ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P),
    HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
    ∀ β : ℝ, 0 < β →
    (∫ y in Iio (0 : ℝ),
        (Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)) / β ∂D.triplet.levyMeasure) =
        (∫ y in Ioo (-1 : ℝ) 0,
          (Real.exp (β * y) - 1 - β * y) / β ∂D.triplet.levyMeasure) +
        (∫ y in Iic (-1 : ℝ),
          (Real.exp (β * y) - 1) / β ∂D.triplet.levyMeasure) →
    (∫ x, (Real.exp (β * x) - 1 -
        (if -1 < x then β * x else 0)) ∂D.triplet.levyMeasure) / β =
      (∫ x in Set.Ioo (-1 : ℝ) 0,
        ((Real.exp (β * x) - 1) / β - x) ∂D.triplet.levyMeasure) +
      (∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure) := by
  sorry

end Kyprianou.Ch08.StageB
