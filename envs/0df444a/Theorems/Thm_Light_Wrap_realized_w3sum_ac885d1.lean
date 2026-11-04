-- Prove2me | Theorems.Thm_Light_Wrap_realized_w3sum_ac885d1
-- name    : Light.Wrap.realized_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:55.032009+00:00
-- url     : https://prove2.me/theorems/07b7eea4-835f-4f9e-a159-1023b0c83ee0
-- title:
--   Wrap: realized
-- statement:
--   **If the task is solved in time T, the problem is solved on the word RAM within a constant times
--   T.**
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L352-L364
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L352-L364

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
open Light.Wrap
variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}

theorem Light.Wrap.realized_w3sum_ac885d1 (w : Wrap Q task dec) {T : ℕ → ℝ → ℝ} (h : SolvedIn task T) : Realized Q T := by sorry
