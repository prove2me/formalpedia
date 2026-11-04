-- Prove2me | Theorems.Thm_Light_sameFrame_cons_cons
-- name    : Light.sameFrame_cons_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:43.715663+00:00
-- url     : https://prove2.me/theorems/6a656251-54f8-476d-8cf8-0d875dcf2923
-- title:
--   Light: same Frame cons cons
-- statement:
--   Two lists give the same locals if their heads are equal and their tails give the same locals.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L254-L259
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L254-L259

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.sameFrame_cons_cons {a b : ℤ} {l m : List ℤ} :
    SameFrame (a :: l) (b :: m) ↔ a = b ∧ SameFrame l m := by sorry
