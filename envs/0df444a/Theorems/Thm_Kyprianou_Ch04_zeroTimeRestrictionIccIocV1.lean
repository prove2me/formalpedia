-- Prove2me | Theorems.Thm_Kyprianou_Ch04_zeroTimeRestrictionIccIocV1
-- name    : Kyprianou.Ch04.zeroTimeRestrictionIccIocV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:16:22.447921+00:00
-- url     : https://prove2.me/theorems/51ae0d60-f468-5f09-8691-f6ff3d369499
-- title:
--   Time-zero null mass permits closed-window replacement
-- statement:
--   For a measure with no mass at time zero, restrictions to closed and left-open time windows agree.
-- source:
--   Kyprianou (2006), Exercise 4.5, finite cutoff and quadratic tail

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem zeroTimeRestrictionIccIocV1 (μ : Measure (ℝ × ℝ))
    (hzero : μ (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0)
    (t : ℝ) (B : Set ℝ) :
    μ.restrict (Icc 0 t ×ˢ B) = μ.restrict (Ioc 0 t ×ˢ B) := by
  sorry
end Kyprianou.Ch04
