-- Prove2me | Theorems.Thm_Light_Stmt_Runs_ite_pos
-- name    : Light.Stmt.Runs.ite_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:26:37.443099+00:00
-- url     : https://prove2.me/theorems/c24ec77e-922d-4be0-8c4d-3affd7f04fcb
-- title:
--   Runs: ite pos
-- statement:
--   A branch whose test holds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L127-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L127-L130

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Stmt.Runs.ite_pos {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop} (h : s.Runs lim σ R)
    (hc : c.Holds σ := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hs : c.Safe lim σ := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)) :
    (Stmt.ite c s t).Runs lim σ R := by sorry
