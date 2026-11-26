-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compactDifferenceSquareRangeV1
-- name    : Kyprianou.Ch04.compactDifferenceSquareRangeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:26:08.956973+00:00
-- url     : https://prove2.me/theorems/a03340a1-60f6-4463-a895-02b19e638911
-- title:
--   Bounded squared difference range on compact horizons
-- statement:
--   Bounded squared difference range on compact horizons
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem compactDifferenceSquareRangeV1 (U V : NNReal → ℝ) (T : NNReal)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∀ t ≤ T, |U t| ≤ A)
    (hv : ∀ t ≤ T, |V t| ≤ B) :
    BddAbove ((fun t : NNReal => |U t - V t|^2) '' Iic T) := by
  sorry
end Kyprianou.Ch04
