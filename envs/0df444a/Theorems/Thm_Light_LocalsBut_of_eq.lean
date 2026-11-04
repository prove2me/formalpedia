-- Prove2me | Theorems.Thm_Light_LocalsBut_of_eq
-- name    : Light.LocalsBut.of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:53.94374+00:00
-- url     : https://prove2.me/theorems/776d0b3a-82e2-48bd-8102-9ac0acb8ef98
-- title:
--   Locals But: of eq
-- statement:
--   Two lists agree except at `xs` if they give the same locals once these entries are copied.  For
--   two lists that are written out, the hypothesis amounts to the equations between their entries, where
--   an entry that is missing counts as 0.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L301-L306
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L301-L306

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

theorem Light.LocalsBut.of_eq (h : SameFrame (refreshLocals l (frame l') xs) l') :
    LocalsBut xs l (frame l') := by sorry
