-- Prove2me | Theorems.Thm_Light_SolvedIn_mono
-- name    : Light.SolvedIn.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:07:51.823219+00:00
-- url     : https://prove2.me/theorems/37d6b5aa-3b2f-4a45-acd2-c62fec96727e
-- title:
--   Solved In: mono
-- statement:
--   A larger bound on the running time is still a bound on the running time.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L134-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L134-L138

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono

set_option autoImplicit false
section
open Light
open ThreeSumApsp

theorem Light.SolvedIn.mono {task : Task} {T T' : ℕ → ℝ → ℝ} (h : SolvedIn task T)
    (hT : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ u → T n u ≤ T' n u) : SolvedIn task T' := by sorry
