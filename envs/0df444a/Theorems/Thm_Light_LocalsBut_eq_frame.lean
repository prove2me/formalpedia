-- Prove2me | Theorems.Thm_Light_LocalsBut_eq_frame
-- name    : Light.LocalsBut.eq_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:52.58532+00:00
-- url     : https://prove2.me/theorems/01785971-ea8c-456c-b538-095cea24efb8
-- title:
--   Locals But: eq frame
-- statement:
--   Locals that agree with a list except at `xs` are themselves given by a list.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L285-L290
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L285-L290

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

theorem Light.LocalsBut.eq_frame (h : LocalsBut xs l loc) : loc = frame (refreshLocals l loc xs) := by sorry
