-- Prove2me | Theorems.Thm_Light_sameFrame_nil_cons
-- name    : Light.sameFrame_nil_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:43.22744+00:00
-- url     : https://prove2.me/theorems/fbaa6f61-7a21-476d-8ff9-4a6f82f9881c
-- title:
--   Light: same Frame nil cons
-- statement:
--   The empty list gives the same locals as a list all of whose entries are 0.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L270-L275
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L270-L275

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.sameFrame_nil_cons {b : ℤ} {m : List ℤ} :
    SameFrame [] (b :: m) ↔ b = 0 ∧ SameFrame [] m := by sorry
