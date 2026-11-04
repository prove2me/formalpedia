-- Prove2me | Theorems.Thm_Light_cbrtLeast_le
-- name    : Light.cbrtLeast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:20.480731+00:00
-- url     : https://prove2.me/theorems/f3d3b633-c7c2-4cea-bd06-77977d2d1ae6
-- title:
--   Light: cbrt Least le
-- statement:
--   The Light construction uses the cbrt Least le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L152-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L152-L153

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

theorem Light.cbrtLeast_le {n s : ℕ} (h : n ≤ s ^ 3) : cbrtLeast n ≤ s := by sorry
