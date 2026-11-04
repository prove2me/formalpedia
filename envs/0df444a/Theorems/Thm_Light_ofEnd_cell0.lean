-- Prove2me | Theorems.Thm_Light_ofEnd_cell0
-- name    : Light.ofEnd_cell0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:24.696824+00:00
-- url     : https://prove2.me/theorems/6a868f0b-07a6-4f5f-8114-88c20aff72b4
-- title:
--   Light: of End cell0
-- statement:
--   Cell 0 holds the size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L111-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L111-L112

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

theorem Light.ofEnd_cell0 (loc : ℕ → ℤ) : (M (k 0)).val ⟨loc, memOf ((ofEnd Q).input x)⟩ = x.n := by sorry
