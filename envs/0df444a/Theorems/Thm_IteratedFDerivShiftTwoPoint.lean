-- Prove2me | Theorems.Thm_IteratedFDerivShiftTwoPoint
-- name    : IteratedFDerivShiftTwoPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:09:44.67734+00:00
-- url     : https://prove2.me/theorems/5849a093-257b-4069-b03d-a57d32721438
-- title:
--   Iterated FDeriv Shift Two Point: Iterated FDeriv Shift Two Point
-- statement:
--   THE ORDER SHIFT, TWO-POINT FORM: at any two points, the order-`(n+1)` jet difference of `f`
--   has the same norm as the order-`n` jet difference of `fderiv R f`.  Mathlib carries only the
--   one-point companion `norm_iteratedFDeriv_fderiv`; a Holder seminorm IS a two-point difference.
--   Arbitrary normed target, all points, no hypothesis on `f`: the shift is a linear isometry.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IteratedFDerivShiftTwoPoint.lean#L7-L12
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IteratedFDerivShiftTwoPoint.lean#L7-L12

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_IteratedFDerivShiftTwoPoint
set_option autoImplicit false

theorem IteratedFDerivShiftTwoPoint (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : Plane → Z) (n : ℕ) (x y : Plane) :
    ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) f y‖
      = ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ f) y‖ := by sorry
