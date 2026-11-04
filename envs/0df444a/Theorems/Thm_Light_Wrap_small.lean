-- Prove2me | Theorems.Thm_Light_Wrap_small
-- name    : Light.Wrap.small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:50.78997+00:00
-- url     : https://prove2.me/theorems/41533912-f1f5-49d1-9900-4ad89f006965
-- title:
--   Wrap: small
-- statement:
--   The limits are polynomial in the size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L294-L324
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L294-L324

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

theorem Light.Wrap.small (w : Wrap Q task dec) {need : ℕ → ℕ → Need} (hpoly : PolyNeed need) (κ : ℕ) :
    ∃ s k : ℕ, ∀ x : Bounded Q, x.U = x.n ^ κ → Small s k [x.n] (w.limits need x) := by sorry
