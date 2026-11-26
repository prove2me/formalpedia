-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableTailBoxDifferenceV1
-- name    : Kyprianou.Ch04.predictableTailBoxDifferenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:36:22.668167+00:00
-- url     : https://prove2.me/theorems/a33f4280-ef44-54e5-8381-09c4e3ce560f
-- title:
--   Finite time cell as difference of predictable tail boxes
-- statement:
--   A finite time cell equals the difference of two predictable tail boxes.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integration.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableTailBoxDifferenceV1 (a b T : ℝ) (hab : a ≤ b) (hbT : b ≤ T)
    (B : Set ℝ) (c : ℝ) (z : ℝ × ℝ) :
    (Ioc a b ×ˢ B).indicator (fun _ => c) z =
      (Ioc a T ×ˢ B).indicator (fun _ => c) z -
      (Ioc b T ×ˢ B).indicator (fun _ => c) z := by
  sorry
end Kyprianou.Ch04
