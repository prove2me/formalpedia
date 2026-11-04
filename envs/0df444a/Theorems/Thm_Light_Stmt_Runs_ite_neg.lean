-- Prove2me | Theorems.Thm_Light_Stmt_Runs_ite_neg
-- name    : Light.Stmt.Runs.ite_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:26:42.501243+00:00
-- url     : https://prove2.me/theorems/edf6906f-5dbd-4297-a26d-c06cfc84dde1
-- title:
--   Runs: ite neg
-- statement:
--   A branch whose test fails.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L133-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L133-L136

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Stmt.Runs.ite_neg {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop} (h : t.Runs lim σ R)
    (hc : ¬c.Holds σ := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hs : c.Safe lim σ := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)) :
    (Stmt.ite c s t).Runs lim σ R := by sorry
