-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compactPairDifferenceBoundV1
-- name    : Kyprianou.Ch04.compactPairDifferenceBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:19.485078+00:00
-- url     : https://prove2.me/theorems/36152947-a060-46fd-bafa-8b0291f24250
-- title:
--   Compact bounds give finite squared difference supremum
-- statement:
--   Compact bounds give finite squared difference supremum.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem compactPairDifferenceBoundV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : NNReal → Ω → ℝ) (T : NNReal)
    (hu : ∀ᵐ w ∂P, ∃ C : ℝ, ∀ t ≤ T, |U t w| ≤ C)
    (hv : ∀ᵐ w ∂P, ∃ C : ℝ, ∀ t ≤ T, |V t w| ≤ C) :
    ∀ᵐ w ∂P, BddAbove ((fun t : NNReal => |U t w - V t w|^2) '' Iic T) := by
  sorry
end Kyprianou.Ch04
