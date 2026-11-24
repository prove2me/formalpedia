-- Prove2me | Theorems.Thm_MomentComparison_onePointUpper
-- name    : MomentComparison.onePointUpper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:51:12.523789+00:00
-- url     : https://prove2.me/theorems/fc6fdd6d-ef6f-48fa-aee5-5ce9dbc0b52f
-- title:
--   Moment Comparison: one Point Upper
-- statement:
--   An upper bound on the two-point squared moment for an exponent at least two.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/TwoPoint.lean#L354-L359
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/TwoPoint.lean#L354-L359

module
public import Definitions.Def_MomentComparison_Lens
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_TwoPoint
set_option autoImplicit true
@[expose] public section
public section
open Filter Topology Set
open MomentComparison

theorem MomentComparison.onePointUpper {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    ((‖1 + z‖ ^ p + ‖1 - z‖ ^ p) / 2) ^ (2 / p) ≤
      1 + (p - 1) * z.re ^ 2 + z.im ^ 2 := by sorry
