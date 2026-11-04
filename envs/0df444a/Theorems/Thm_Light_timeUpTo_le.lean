-- Prove2me | Theorems.Thm_Light_timeUpTo_le
-- name    : Light.timeUpTo_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:12.216476+00:00
-- url     : https://prove2.me/theorems/0cbc9730-ce7d-493e-abba-92daaa926d2e
-- title:
--   Light: time Up To le
-- statement:
--   What bounds the time for every natural number `U ≤ u` bounds `timeUpTo`.  For a negative `u`
--   there is still `U = 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L152-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L152-L161

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
set_option autoImplicit false
section
open Light
open ThreeSumApsp

theorem Light.timeUpTo_le {Tn : ℕ → ℕ → ℕ} {n : ℕ} {u B : ℝ}
    (h : ∀ U : ℕ, (U : ℝ) ≤ max u 0 → (Tn n U : ℝ) ≤ B) : timeUpTo Tn n u ≤ B := by sorry
