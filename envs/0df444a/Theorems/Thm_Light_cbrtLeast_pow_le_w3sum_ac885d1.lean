-- Prove2me | Theorems.Thm_Light_cbrtLeast_pow_le_w3sum_ac885d1
-- name    : Light.cbrtLeast_pow_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:23.324626+00:00
-- url     : https://prove2.me/theorems/3a6c3df7-f6d6-4bde-a192-b595c4865c8f
-- title:
--   Light: cbrt Least pow le
-- statement:
--   The cube of the rounded cube root is at most 8 n.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L166-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L166-L177

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

theorem Light.cbrtLeast_pow_le_w3sum_ac885d1 (n : ℕ) : cbrtLeast n ^ 3 ≤ 8 * n := by sorry
