-- Prove2me | Theorems.Thm_Kyprianou_Ch04_subtractLinearHasDerivV1
-- name    : Kyprianou.Ch04.subtractLinearHasDerivV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:42:25.928056+00:00
-- url     : https://prove2.me/theorems/43460dec-f417-5fce-a35a-de1d6c090143
-- title:
--   Derivative of the linear residual
-- statement:
--   Derivative of the linear residual
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, Taylor estimate decomposition.

import Mathlib
open Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem subtractLinearHasDerivV1 (f : ℝ → ℝ) (x u : ℝ) (hf : Differentiable ℝ f) :
    HasDerivAt (fun v => f v - v * deriv f x) (deriv f u - deriv f x) u := by
  sorry
end Kyprianou.Ch04
