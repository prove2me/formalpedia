-- Prove2me | Theorems.Thm_Light_Meets_mono_const
-- name    : Light.Meets.mono_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:33:09.321057+00:00
-- url     : https://prove2.me/theorems/4cc72c2b-4cd0-4977-bb28-1ec90c357a31
-- title:
--   Meets: mono const
-- statement:
--   A specification whose time is a constant times a shape holds for every larger constant.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Calls.lean#L67-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Calls.lean#L67-L69

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

theorem Light.Meets.mono_const {c c' S : ℕ} (h : Meets lim P p d vals μ (c * S) R) (hc : c ≤ c') :
    Meets lim P p d vals μ (c' * S) R := by sorry
