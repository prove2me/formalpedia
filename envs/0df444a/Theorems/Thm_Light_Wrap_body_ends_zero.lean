-- Prove2me | Theorems.Thm_Light_Wrap_body_ends_zero
-- name    : Light.Wrap.body_ends_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:47.399953+00:00
-- url     : https://prove2.me/theorems/9d64b261-6c35-4d26-b99f-00f46695bc68
-- title:
--   Wrap: body ends zero
-- statement:
--   The run of the outermost procedure on an instance of size 0.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L268-L281
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L268-L281

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

theorem Light.Wrap.body_ends_zero (w : Wrap Q task dec) (P : Program) (p κ : ℕ) (x : Bounded Q) (hn : x.n = 0)
    {need : ℕ → ℕ → Need} {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ 9 (Answered x dec) := by sorry
