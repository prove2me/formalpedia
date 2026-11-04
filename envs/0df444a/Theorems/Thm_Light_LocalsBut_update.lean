-- Prove2me | Theorems.Thm_Light_LocalsBut_update
-- name    : Light.LocalsBut.update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:52.575824+00:00
-- url     : https://prove2.me/theorems/c533c255-cde2-43f9-82b3-ff94a3e9480f
-- title:
--   Locals But: update
-- statement:
--   An assignment, on both sides.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L293-L296
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L293-L296

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

theorem Light.LocalsBut.update (h : LocalsBut xs l loc) (x : ℕ) (z : ℤ) :
    LocalsBut xs (setLocal l x z) (Function.update loc x z) := by sorry
