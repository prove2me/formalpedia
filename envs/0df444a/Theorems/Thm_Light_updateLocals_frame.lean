-- Prove2me | Theorems.Thm_Light_updateLocals_frame
-- name    : Light.updateLocals_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:36.439099+00:00
-- url     : https://prove2.me/theorems/e90c12f3-f81a-4a18-a3b1-0157e3d8f6ec
-- title:
--   Light: update Locals frame
-- statement:
--   Several assignments, in terms of the list.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L225-L229
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L225-L229

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.updateLocals_frame : ∀ (ps : List (ℕ × ℤ)) (l : List ℤ),
    updateLocals (frame l) ps = frame (setLocals l ps)
  := by sorry
