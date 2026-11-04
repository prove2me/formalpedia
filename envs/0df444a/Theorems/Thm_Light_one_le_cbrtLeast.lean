-- Prove2me | Theorems.Thm_Light_one_le_cbrtLeast
-- name    : Light.one_le_cbrtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:19.471591+00:00
-- url     : https://prove2.me/theorems/a70f59d6-9411-4980-b079-bd9ea76b25cc
-- title:
--   Light: one le cbrt Least
-- statement:
--   The number ⌈n^{1/3}⌉ is at least 1 for n ≥ 1.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L159-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L159-L163

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

theorem Light.one_le_cbrtLeast {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtLeast n := by sorry
