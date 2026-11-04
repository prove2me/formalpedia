-- Prove2me | Theorems.Thm_Light_sameFrame_nil
-- name    : Light.sameFrame_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:47.370105+00:00
-- url     : https://prove2.me/theorems/23a8fae9-004b-450f-b44e-4750af18742e
-- title:
--   Light: same Frame nil
-- statement:
--   The empty list gives the same locals as itself.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L251-L251
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L251-L251

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.sameFrame_nil : SameFrame [] [] := by sorry

attribute [defeq] Light.sameFrame_nil
