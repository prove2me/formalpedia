-- Prove2me | Theorems.Thm_Light_SolvesN_append
-- name    : Light.SolvesN.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:07:49.731617+00:00
-- url     : https://prove2.me/theorems/c675d1db-9a4f-4ae2-acc5-3bd05ad8ad6f
-- title:
--   Solves N: append
-- statement:
--   A solver stays a solver when procedures are appended to its program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L216-L221
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L216-L221

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append

set_option autoImplicit false
section
open Light
open ThreeSumApsp

theorem Light.SolvesN.append {task : TaskN} {P : Program} {p : ℕ} {T : List ℕ → ℕ} {need : List ℕ → Need}
    (h : SolvesN task P p T need) (R : Program) : SolvesN task (P ++ R) p T need := by sorry
