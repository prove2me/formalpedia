-- Prove2me | Theorems.Thm_MomentComparison_arg_cpow_ofReal
-- name    : MomentComparison.arg_cpow_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:29.674726+00:00
-- url     : https://prove2.me/theorems/74b3bfcc-df61-41e6-a0f7-50bbc5f697f9
-- title:
--   Moment Comparison: arg cpow of Real
-- statement:
--   Positive real powers scale the argument while it stays in its principal interval.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/ComplexPower.lean#L33-L38
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/ComplexPower.lean#L33-L38

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Definitions.Def_MomentComparison_ComplexPower
set_option autoImplicit true
@[expose] public section
public section
open MomentComparison

theorem MomentComparison.arg_cpow_ofReal {z : ℂ} (hz : z ≠ 0) {b : ℝ}
    (hl : -Real.pi < z.arg * b) (hu : z.arg * b ≤ Real.pi) :
    (z ^ (b : ℂ)).arg = z.arg * b := by sorry
