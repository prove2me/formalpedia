-- Prove2me | Theorems.Thm_Light_Ends_seqSelf
-- name    : Light.Ends.seqSelf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:27:22.674358+00:00
-- url     : https://prove2.me/theorems/874e0dc8-044e-4337-a7e2-b841506a5dbe
-- title:
--   Ends: seq Self
-- statement:
--   A program that is defined as a sequence may be treated as the sequence.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L195-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L195-L197

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q := by sorry
