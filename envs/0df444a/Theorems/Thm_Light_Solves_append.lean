-- Prove2me | Theorems.Thm_Light_Solves_append
-- name    : Light.Solves.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:07:54.599087+00:00
-- url     : https://prove2.me/theorems/431858d7-211e-4cdd-8683-6d816b45a792
-- title:
--   Solves: append
-- statement:
--   A solver stays a solver when procedures are appended to its program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L108-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L108-L113

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

theorem Light.Solves.append {task : Task} {P : Program} {p : ℕ} {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : Solves task P p T need) (R : Program) : Solves task (P ++ R) p T need := by sorry
