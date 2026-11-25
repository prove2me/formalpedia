-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTimeDerivativeBoundV1
-- name    : Kyprianou.Ch04.exercise42LipschitzTimeDerivativeBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:57:58.044363+00:00
-- url     : https://prove2.me/theorems/1fca3e41-7629-4e0f-ba33-1f519846228a
-- title:
--   Derivative bound for NNReal-Lipschitz path on real time
-- statement:
--   The derivative of the positive-time extension of an NNReal Lipschitz path, evaluated anywhere on the real line, has norm bounded by its original Lipschitz constant.
-- source:
--   Lipschitz Stieltjes calculus support for Kyprianou (2006), Ch04 Exercise 4.2.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzTimeDerivativeBoundV1
    (U : NNReal → ℝ) (K : NNReal) (hU : LipschitzWith K U) (u : ℝ) :
    ‖deriv (fun z : ℝ => U z.toNNReal) u‖ ≤ (K : ℝ) := by
  sorry
