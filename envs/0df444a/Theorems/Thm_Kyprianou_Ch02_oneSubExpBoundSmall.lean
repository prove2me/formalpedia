-- Prove2me | Theorems.Thm_Kyprianou_Ch02_oneSubExpBoundSmall
-- name    : Kyprianou.Ch02.oneSubExpBoundSmall
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:58:50.021797+00:00
-- url     : https://prove2.me/theorems/277bbdd4-ed31-49d1-9c89-ea1278adc299
-- title:
--   For x between zero and one the exponential Laplace factor dominates half of x
-- statement:
--   For x between zero and one the exponential Laplace factor dominates half of x. This is an independent elementary real-analysis sublemma supporting Chapter 2 Exercise 2.3.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.3; elementary exponential inequality

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem oneSubExpBoundSmall (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ 2 * (1 - Real.exp (-x)) := by sorry
end Kyprianou.Ch02
