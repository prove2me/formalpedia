-- Prove2me | Theorems.Thm_Light_Wrap_body_ends
-- name    : Light.Wrap.body_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:45.224555+00:00
-- url     : https://prove2.me/theorems/3d50eeb9-a964-490a-8c9a-3b864584dfb7
-- title:
--   Wrap: body ends
-- statement:
--   The run of the outermost procedure on an instance of size at least 1.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L229-L265
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L229-L265

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

theorem Light.Wrap.body_ends (w : Wrap Q task dec) {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hsol : Solves task P p Tn need) (κ : ℕ) (x : Bounded Q) (hn : 1 ≤ x.n) (hU : x.U = x.n ^ κ)
    {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ (Tn x.n x.U + w.bodySteps κ) (Answered x dec) := by sorry
