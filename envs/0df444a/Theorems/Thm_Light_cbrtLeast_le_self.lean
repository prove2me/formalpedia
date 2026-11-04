-- Prove2me | Theorems.Thm_Light_cbrtLeast_le_self
-- name    : Light.cbrtLeast_le_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:22.843903+00:00
-- url     : https://prove2.me/theorems/2fe143a3-9b55-4455-808d-ccd16598582c
-- title:
--   Light: cbrt Least le self
-- statement:
--   The Light construction uses the cbrt Least le self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L155-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L155-L156

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Logs

theorem Light.cbrtLeast_le_self (n : ℕ) : cbrtLeast n ≤ n := by sorry
