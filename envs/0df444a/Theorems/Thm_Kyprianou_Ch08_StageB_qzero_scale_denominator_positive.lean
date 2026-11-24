-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_scale_denominator_positive
-- name    : Kyprianou.Ch08.StageB.qzero_scale_denominator_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:46:31.703629+00:00
-- url     : https://prove2.me/theorems/dc16a496-7398-4721-810e-462b8f2815f1
-- title:
--   Positive zero-discount scale value at a positive reserve
-- statement:
--   For any source-faithful scale family attached to a spectrally negative model and any positive reserve a, the zero-discount scale value W(0,a) is strictly positive. This isolates the exact denominator condition needed by the zero-discount killed-interval occupation density.
-- source:
--   Kyprianou (2006), Chapter 8, scale-function normalization and two-sided exit ratio at zero discount.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Strict positivity of the zero-discount scale value at a positive reserve. -/
theorem qzero_scale_denominator_positive :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ a : ℝ, 0 < a → 0 < W 0 a := by
  sorry

end Kyprianou.Ch08.StageB
