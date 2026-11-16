-- Prove2me | Theorems.Thm_Kyprianou_Ch02_oneSubExpUpperBound
-- name    : Kyprianou.Ch02.oneSubExpUpperBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:34:07.898199+00:00
-- url     : https://prove2.me/theorems/ae8ea4d0-0146-4e8a-8d74-d8d1e2b30a68
-- title:
--   Upper comparison of Laplace integrand by truncated positive input
-- statement:
--   For x nonnegative and phi positive, 1-exp(-phi*x) is at most max(1,phi)*min(1,x). Used for Chapter 2 Exercise 2.3 to dominate a Laplace compensator by the truncated Levy integrability kernel.
-- source:
--   Kyprianou (2006), Chapter 2 Exercise 2.3, scalar inequality

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem oneSubExpUpperBound (x φ : ℝ)
    (hx : 0 ≤ x) (hφ : 0 < φ) :
    1 - Real.exp (-φ * x) ≤ max 1 φ * min 1 x := by sorry
end Kyprianou.Ch02
