-- Prove2me | Theorems.Thm_Light_sameFrame_cons_nil
-- name    : Light.sameFrame_cons_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:44.42477+00:00
-- url     : https://prove2.me/theorems/282d939d-53c5-4ece-ad52-464024ab3445
-- title:
--   Light: same Frame cons nil
-- statement:
--   A list gives the same locals as the empty list if all its entries are 0.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L262-L267
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L262-L267

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.sameFrame_cons_nil {a : ℤ} {l : List ℤ} :
    SameFrame (a :: l) [] ↔ a = 0 ∧ SameFrame l [] := by sorry
