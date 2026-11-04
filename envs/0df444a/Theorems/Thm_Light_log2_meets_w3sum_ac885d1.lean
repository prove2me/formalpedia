-- Prove2me | Theorems.Thm_Light_log2_meets_w3sum_ac885d1
-- name    : Light.log2_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:18.157328+00:00
-- url     : https://prove2.me/theorems/6b82b121-d0f5-4fa8-8bd3-d70d6c0b10da
-- title:
--   Light: log2 meets
-- statement:
--   **log2(x)** returns ⌊log₂ x⌋ and leaves the memory as it is.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L63-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L63-L94

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

theorem Light.log2_meets_w3sum_ac885d1 {p x : ℕ} (hp : P[p]? = some log2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (log2Time x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ := by sorry
