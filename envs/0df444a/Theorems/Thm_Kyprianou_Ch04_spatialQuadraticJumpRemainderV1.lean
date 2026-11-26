-- Prove2me | Theorems.Thm_Kyprianou_Ch04_spatialQuadraticJumpRemainderV1
-- name    : Kyprianou.Ch04.spatialQuadraticJumpRemainderV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:39:30.315815+00:00
-- url     : https://prove2.me/theorems/cde093b8-7065-5577-ba6d-c3f03fb0f3ce
-- title:
--   Quadratic jump Taylor remainder under a bounded second derivative
-- statement:
--   A twice continuously differentiable real function with globally bounded second derivative has absolute first-order Taylor remainder bounded by K times the square of the increment.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5 and Theorem 4.3, supporting Taylor estimate.

import Mathlib
open Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem spatialQuadraticJumpRemainderV1 (f : ℝ → ℝ) (K x z : ℝ)
    (h : ContDiff ℝ 2 f) (hK : 0 ≤ K)
    (hbound : ∀ u, |deriv (deriv f) u| ≤ K) :
    |f (x + z) - f x - z * deriv f x| ≤ K * z ^ 2 := by
  sorry
end Kyprianou.Ch04
