-- Prove2me | Theorems.Thm_MomentComparison_cpow_div_of_arg_sub
-- name    : MomentComparison.cpow_div_of_arg_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:31.881269+00:00
-- url     : https://prove2.me/theorems/81cb308c-b145-489b-abd1-f0ec454b6a81
-- title:
--   Moment Comparison: cpow div of arg sub
-- statement:
--   Principal complex powers distribute over division within a common branch.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/ComplexPower.lean#L21-L30
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/ComplexPower.lean#L21-L30

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Definitions.Def_MomentComparison_ComplexPower
set_option autoImplicit true
@[expose] public section
public section
open MomentComparison

theorem MomentComparison.cpow_div_of_arg_sub {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlo : -Real.pi < x.arg - y.arg) (hhi : x.arg - y.arg ≤ Real.pi) (b : ℂ) :
    (x / y) ^ b = x ^ b / y ^ b := by sorry
