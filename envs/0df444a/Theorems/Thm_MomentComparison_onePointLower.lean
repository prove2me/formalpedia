-- Prove2me | Theorems.Thm_MomentComparison_onePointLower
-- name    : MomentComparison.onePointLower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:51:11.937892+00:00
-- url     : https://prove2.me/theorems/77c2ec91-69b0-4f23-bb60-c738e3312358
-- title:
--   Moment Comparison: one Point Lower
-- statement:
--   A lower bound on the two-point squared moment for an exponent at most two.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/TwoPoint.lean#L362-L367
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/TwoPoint.lean#L362-L367

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

theorem MomentComparison.onePointLower {p : ℝ} (hp : 1 < p) (hp' : p ≤ 2) (z : ℂ) :
    1 + (p - 1) * z.re ^ 2 + z.im ^ 2 ≤
      ((‖1 + z‖ ^ p + ‖1 - z‖ ^ p) / 2) ^ (2 / p) := by sorry
