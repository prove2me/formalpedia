-- Prove2me | Theorems.Thm_Light_verdictOf_flag
-- name    : Light.verdictOf_flag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:43.588885+00:00
-- url     : https://prove2.me/theorems/e0347153-8089-4d85-b3cd-4492b2324bd6
-- title:
--   Light: verdict Of flag
-- statement:
--   The verdict that belongs to the result of a decision procedure.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L97-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L97-L102

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.verdictOf_flag (p : Prop) : verdictOf true (ThreeSumApsp.flag p) = true ↔ p := by sorry
