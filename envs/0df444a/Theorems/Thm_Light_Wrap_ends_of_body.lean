-- Prove2me | Theorems.Thm_Light_Wrap_ends_of_body
-- name    : Light.Wrap.ends_of_body
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:50.435349+00:00
-- url     : https://prove2.me/theorems/a10b328e-faaa-4f6a-8652-fa3cd25fb8ff
-- title:
--   Wrap: ends of body
-- statement:
--   The outermost call, from the run of its procedure.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L284-L291
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L284-L291

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

theorem Light.Wrap.ends_of_body (w : Wrap Q task dec) {P : Program} {p κ T : ℕ} (x : Bounded Q)
    {need : ℕ → ℕ → Need}
    (h : Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ T (Answered x dec)) :
    Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 0 (mainStmt P.length)
      ⟨frame [0, 0, 0], memOf ((ofEnd Q).input x)⟩ (T + 4) (Answered x dec) := by sorry
