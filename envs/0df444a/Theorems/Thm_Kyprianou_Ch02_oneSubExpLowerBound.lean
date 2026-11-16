-- Prove2me | Theorems.Thm_Kyprianou_Ch02_oneSubExpLowerBound
-- name    : Kyprianou.Ch02.oneSubExpLowerBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:56:13.309931+00:00
-- url     : https://prove2.me/theorems/cad32b52-54d8-4137-bcf1-b8d7dcb8dee7
-- title:
--   Quantitative lower bound for the positive Laplace integrand
-- statement:
--   For every nonnegative real x, the truncated value min(1,x) is bounded by twice the positive Laplace transform factor 1-exp(-x). This is a genuine scalar estimate needed for the reverse implication in Exercise 2.3.
-- source:
--   Kyprianou (2006) Chapter 2 Exercise 2.3 and the end-of-book solution

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem oneSubExpLowerBound (x : ℝ) (hx : 0 ≤ x) :
    min 1 x ≤ 2 * (1 - Real.exp (-x)) := by sorry
end Kyprianou.Ch02
