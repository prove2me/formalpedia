-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedSecondDerivativeLipschitzV1
-- name    : Kyprianou.Ch04.boundedSecondDerivativeLipschitzV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:42:28.872355+00:00
-- url     : https://prove2.me/theorems/e9b75e08-0c80-4b7e-a407-dbfce48474c9
-- title:
--   Bounded second derivative implies Lipschitz first derivative
-- statement:
--   Bounded second derivative implies Lipschitz first derivative
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, Taylor estimate decomposition.

import Mathlib
open Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedSecondDerivativeLipschitzV1 (f : ℝ → ℝ) (K x u : ℝ)
    (h : ContDiff ℝ 2 f) (hbound : ∀ v, |deriv (deriv f) v| ≤ K) :
    |deriv f u - deriv f x| ≤ K * |u - x| := by
  sorry
end Kyprianou.Ch04
