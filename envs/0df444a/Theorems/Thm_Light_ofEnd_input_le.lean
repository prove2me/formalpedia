-- Prove2me | Theorems.Thm_Light_ofEnd_input_le
-- name    : Light.ofEnd_input_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:47.605688+00:00
-- url     : https://prove2.me/theorems/93c43a00-757a-4127-90f4-a7669e6ed47a
-- title:
--   Light: of End input le
-- statement:
--   All cells of the input are within the size and the bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L115-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L115-L123

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

theorem Light.ofEnd_input_le : ∀ a ∈ (ofEnd Q).input x, |a| ≤ ((x.n + x.U + 1 : ℕ) : ℤ) := by sorry
