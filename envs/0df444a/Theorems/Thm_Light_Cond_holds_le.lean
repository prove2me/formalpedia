-- Prove2me | Theorems.Thm_Light_Cond_holds_le
-- name    : Light.Cond.holds_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:42.376255+00:00
-- url     : https://prove2.me/theorems/f0c9b5a2-a312-4b79-8c69-24a882ff1d95
-- title:
--   Cond: holds le
-- statement:
--   The test a ≤ b holds if and only if a ≤ b.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L238-L239
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L238-L239

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

theorem Light.Cond.holds_le {σ : State} {a b : Expr} : (a ≤' b).Holds σ ↔ a.val σ ≤ b.val σ := by sorry
