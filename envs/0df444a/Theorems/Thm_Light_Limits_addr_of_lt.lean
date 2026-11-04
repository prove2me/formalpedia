-- Prove2me | Theorems.Thm_Light_Limits_addr_of_lt
-- name    : Light.Limits.addr_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:46.484394+00:00
-- url     : https://prove2.me/theorems/07c86cde-98e1-4986-80af-0aaf56ee9992
-- title:
--   Limits: addr of lt
-- statement:
--   A natural number below the size of the memory is an address, and fits in a word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L274-L277
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L274-L277

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

theorem Light.Limits.addr_of_lt (hw : (lim.space : ℤ) ≤ lim.word) {x : ℕ} (hx : x < lim.space) :
    lim.Addr (x : ℤ) ∧ |(x : ℤ)| ≤ lim.word := by sorry
