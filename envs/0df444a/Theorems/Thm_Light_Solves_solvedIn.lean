-- Prove2me | Theorems.Thm_Light_Solves_solvedIn
-- name    : Light.Solves.solvedIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:08.363402+00:00
-- url     : https://prove2.me/theorems/1681096f-a3f4-4774-8fa6-316d73b43032
-- title:
--   Solves: solved In
-- statement:
--   A solver with a polynomially bounded need solves its task in its own time.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L164-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L164-L166

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
set_option autoImplicit false
section
open Light
open ThreeSumApsp

theorem Light.Solves.solvedIn {task : Task} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hs : Solves task P p Tn need) (hp : PolyNeed need) : SolvedIn task (timeUpTo Tn) := by sorry
