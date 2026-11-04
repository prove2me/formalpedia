-- Prove2me | Theorems.Thm_Light_Limits_abs_le_of_le
-- name    : Light.Limits.abs_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:47.711368+00:00
-- url     : https://prove2.me/theorems/9d8001d8-824c-427f-84f1-131c5ef8983f
-- title:
--   Limits: abs le of le
-- statement:
--   A natural number at most the size of the memory fits in a word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L280-L283
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L280-L283

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

theorem Light.Limits.abs_le_of_le (hw : (lim.space : ℤ) ≤ lim.word) {x : ℕ} (hx : x ≤ lim.space) :
    |(x : ℤ)| ≤ lim.word := by sorry
