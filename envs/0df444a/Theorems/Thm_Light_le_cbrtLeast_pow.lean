-- Prove2me | Theorems.Thm_Light_le_cbrtLeast_pow
-- name    : Light.le_cbrtLeast_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:22.699009+00:00
-- url     : https://prove2.me/theorems/210b6ad8-0b52-4382-9bf8-c2bb41672cb9
-- title:
--   Light: le cbrt Least pow
-- statement:
--   The Light construction uses the le cbrt Least pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L147-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L147-L147

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

theorem Light.le_cbrtLeast_pow (n : ℕ) : n ≤ cbrtLeast n ^ 3 := by sorry
