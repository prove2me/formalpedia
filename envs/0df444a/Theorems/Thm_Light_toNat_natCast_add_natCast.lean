-- Prove2me | Theorems.Thm_Light_toNat_natCast_add_natCast
-- name    : Light.toNat_natCast_add_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:44.7442+00:00
-- url     : https://prove2.me/theorems/db1579e0-a0a5-49a0-945b-d3f09f1f594c
-- title:
--   Light: to Nat nat Cast add nat Cast
-- statement:
--   The natural number behind an address that is a sum of two natural numbers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L257-L258
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L257-L258

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
public import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame

theorem Light.toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by sorry
