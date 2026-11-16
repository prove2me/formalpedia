-- Prove2me | Theorems.Thm_Kyprianou_Ch02_oneSubExpBoundLarge
-- name    : Kyprianou.Ch02.oneSubExpBoundLarge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:58:51.827273+00:00
-- url     : https://prove2.me/theorems/68a9dedc-97ff-4472-81d0-043cf017a651
-- title:
--   For x at least one the exponential Laplace factor is at least one half
-- statement:
--   For x at least one the exponential Laplace factor is at least one half. This is an independent elementary real-analysis sublemma supporting Chapter 2 Exercise 2.3.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.3; elementary exponential inequality

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem oneSubExpBoundLarge (x : ℝ) (hx1 : 1 ≤ x) :
    1 ≤ 2 * (1 - Real.exp (-x)) := by sorry
end Kyprianou.Ch02
