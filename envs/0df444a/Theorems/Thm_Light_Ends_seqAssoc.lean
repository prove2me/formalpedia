-- Prove2me | Theorems.Thm_Light_Ends_seqAssoc
-- name    : Light.Ends.seqAssoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:27:03.192884+00:00
-- url     : https://prove2.me/theorems/5c5689a5-c8a4-4a54-93bf-cc48a46ebbb2
-- title:
--   Ends: seq Assoc
-- statement:
--   Brackets do not matter: a piece of several statements, followed by the rest of the program, is
--   run statement by statement.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L172-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean#L172-L178

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by sorry
