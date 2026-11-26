-- Prove2me | Theorems.Thm_Kyprianou_Ch04_spatialRemainderFromDerivativeBudgetV1
-- name    : Kyprianou.Ch04.spatialRemainderFromDerivativeBudgetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:42:27.722276+00:00
-- url     : https://prove2.me/theorems/f2cc5a0b-0e03-4aa3-805b-a852989c525a
-- title:
--   Quadratic residual from a derivative difference budget
-- statement:
--   Quadratic residual from a derivative difference budget
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, Taylor estimate decomposition.

import Mathlib
open Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem spatialRemainderFromDerivativeBudgetV1 (f : ℝ → ℝ) (K x z : ℝ)
    (hK : 0 ≤ K)
    (hLip : ∀ u, |deriv f u - deriv f x| ≤ K * |u - x|)
    (hD : ∀ u, HasDerivAt (fun v => f v - v * deriv f x)
      (deriv f u - deriv f x) u) :
    |f (x + z) - f x - z * deriv f x| ≤ K * z ^ 2 := by
  sorry
end Kyprianou.Ch04
