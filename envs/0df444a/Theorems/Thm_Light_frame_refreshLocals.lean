-- Prove2me | Theorems.Thm_Light_frame_refreshLocals
-- name    : Light.frame_refreshLocals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:41.393606+00:00
-- url     : https://prove2.me/theorems/44111959-2391-4c1b-a20d-7d0e05c19d53
-- title:
--   Light: frame refresh Locals
-- statement:
--   Reading a local of `refreshLocals l loc xs`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L237-L245
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L237-L245

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.frame_refreshLocals (loc : ℕ → ℤ) (y : ℕ) : ∀ (xs : List ℕ) (l : List ℤ),
    frame (refreshLocals l loc xs) y = if y ∈ xs then loc y else frame l y
  := by sorry
