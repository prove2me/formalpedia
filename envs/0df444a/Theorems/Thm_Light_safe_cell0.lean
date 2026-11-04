-- Prove2me | Theorems.Thm_Light_safe_cell0
-- name    : Light.safe_cell0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:29.532173+00:00
-- url     : https://prove2.me/theorems/43c1ed55-e882-441c-acf5-25fe04045d05
-- title:
--   Light: safe cell0
-- statement:
--   Cell 0 may be read.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L126-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L126-L129

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
variable {Q : EndStatement.Problem} (x : Bounded Q)

theorem Light.safe_cell0 {lim : Limits} {σ : State} (h0 : 0 ≤ lim.word) (h1 : 1 ≤ lim.space) :
    (M (k 0)).Safe lim σ := by sorry
