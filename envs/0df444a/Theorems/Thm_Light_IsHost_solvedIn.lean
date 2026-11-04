-- Prove2me | Theorems.Thm_Light_IsHost_solvedIn
-- name    : Light.IsHost.solvedIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:28.117284+00:00
-- url     : https://prove2.me/theorems/8cb62611-7542-4310-b383-29e1fc0dafe2
-- title:
--   Is Host: solved In
-- statement:
--   From a host to a transfer of running times.  What remains is arithmetic: a bound for the host's
--   time function, given a bound for the solver's.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L181-L189
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L181-L189

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
set_option autoImplicit false
section
open Light
open ThreeSumApsp

theorem Light.IsHost.solvedIn {lower upper : Task} {time : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ}
    {need : (ℕ → ℕ → Need) → ℕ → ℕ → Need} (h : IsHost lower upper time need) {T T' : ℕ → ℝ → ℝ}
    (hs : SolvedIn lower T)
    (hb : ∀ Tn : ℕ → ℕ → ℕ, (∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤
    T n u) → ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (time Tn n U : ℝ) ≤ T' n u) :
    SolvedIn upper T' := by sorry
