-- Prove2me | Theorems.Thm_MomentComparison_arg_div_of_arg_sub
-- name    : MomentComparison.arg_div_of_arg_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:22.162966+00:00
-- url     : https://prove2.me/theorems/222e4a45-77f4-444f-8ee9-fe5784b8f29a
-- title:
--   Moment Comparison: arg div of arg sub
-- statement:
--   Division subtracts principal arguments when the difference lies in the principal interval.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/ComplexPower.lean#L10-L18
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/ComplexPower.lean#L10-L18

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Definitions.Def_MomentComparison_ComplexPower
set_option autoImplicit true
@[expose] public section
public section
open MomentComparison

theorem MomentComparison.arg_div_of_arg_sub {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlo : -Real.pi < x.arg - y.arg) (hhi : x.arg - y.arg ≤ Real.pi) :
    (x / y).arg = x.arg - y.arg := by sorry
