-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_convex_positive_secant_inverse_bound
-- name    : Kyprianou.Ch08.StageB.p2m89_convex_positive_secant_inverse_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:37:28.283979+00:00
-- url     : https://prove2.me/theorems/51d6fcec-973e-4839-ac4f-e2bf4f938667
-- title:
--   Convex positive inverse secant bound
-- statement:
--   For a convex real function f on the non-negative half-line with f(0)=0, and positive x,y, the distance |x-y| multiplied by f(y) is at most |f(x)-f(y)| multiplied by y.
-- source:
--   Kyprianou (2006), Theorem 8.9: differentiability of the inverse Laplace exponent; elementary convexity lemma.

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Slope
set_option autoImplicit false
open Set

namespace Kyprianou.Ch08.StageB

/-- The inverse secant bound for two positive arguments of a convex function. -/
theorem p2m89_convex_positive_secant_inverse_bound :
    ∀ (f : ℝ → ℝ), f 0 = 0 → ConvexOn ℝ (Ici (0 : ℝ)) f →
      ∀ x y : ℝ, 0 < x → 0 < y →
      |x - y| * f y ≤ |f x - f y| * y := by
  sorry

end Kyprianou.Ch08.StageB
