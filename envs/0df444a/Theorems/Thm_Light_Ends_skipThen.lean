-- Prove2me | Theorems.Thm_Light_Ends_skipThen
-- name    : Light.Ends.skipThen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:27:08.433292+00:00
-- url     : https://prove2.me/theorems/f3a8b6f3-5422-40b6-9905-abb7ddd6bec9
-- title:
--   Ends: skip Then
-- statement:
--   A `skip` before the rest of the program takes no step.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L181-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L181-L183

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d (.skip ;; s) σ T Q := by sorry
