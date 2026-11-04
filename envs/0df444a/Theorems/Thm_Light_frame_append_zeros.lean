-- Prove2me | Theorems.Thm_Light_frame_append_zeros
-- name    : Light.frame_append_zeros
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:30:21.803205+00:00
-- url     : https://prove2.me/theorems/b999f417-2622-46df-bbb0-fd85669e1f77
-- title:
--   Light: frame append zeros
-- statement:
--   Zeros at the end of the list do not matter.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L76-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L76-L83

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by sorry
