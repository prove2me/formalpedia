-- Prove2me | Theorems.Thm_Kyprianou_Ch01_strictConvex_positiveRoot_iff_derivativeNegative
-- name    : Kyprianou.Ch01.strictConvex_positiveRoot_iff_derivativeNegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T12:06:44.177135+00:00
-- url     : https://prove2.me/theorems/80c636ab-5b1f-4dc2-af40-5253e123bd55
-- title:
--   Strictly convex divergent function has a positive root exactly when its right derivative at zero is negative
-- statement:
--   For a strictly convex continuous real function on the nonnegative reals, vanishing at zero and diverging to infinity, existence of a positive zero is equivalent to a strictly negative right derivative at zero.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i), Cramer positive root existence criterion

import Mathlib
open MeasureTheory Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.strictConvex_positiveRoot_iff_derivativeNegative
    (f : ℝ → ℝ) (d : ℝ)
    (hconv : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) f)
    (hzero : f 0 = 0)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (hlarge : Tendsto f atTop atTop)
    (hd : HasDerivWithinAt f d (Set.Ici (0 : ℝ)) 0) :
    ((∃ theta : ℝ, 0 < theta ∧ f theta = 0) ↔ d < 0) := by sorry
