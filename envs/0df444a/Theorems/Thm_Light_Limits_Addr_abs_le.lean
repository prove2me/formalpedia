-- Prove2me | Theorems.Thm_Light_Limits_Addr_abs_le
-- name    : Light.Limits.Addr.abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:46.062249+00:00
-- url     : https://prove2.me/theorems/58186652-81fb-4d44-9f03-aa7abf6721de
-- title:
--   Addr: abs le
-- statement:
--   An address fits in a word if the memory is not larger than the largest word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L269-L271
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L269-L271

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

theorem Light.Limits.Addr.abs_le {a : ℤ} (h : lim.Addr a) (hw : (lim.space : ℤ) ≤ lim.word) :
    |a| ≤ lim.word := by sorry
