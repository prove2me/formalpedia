-- Prove2me | Theorems.Thm_Light_cbrtCeil_meets_w3sum_ac885d1
-- name    : Light.cbrtCeil_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:27.16496+00:00
-- url     : https://prove2.me/theorems/21a23aa5-3ee6-462b-92d1-32e799bb7702
-- title:
--   Light: cbrt Ceil meets
-- statement:
--   **cbrtCeil(n)** returns the least s with s³ ≥ n and leaves the memory as it is.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L208-L237
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L208-L237

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

theorem Light.cbrtCeil_meets_w3sum_ac885d1 {p n : ℕ} (hp : P[p]? = some cbrtCeilBody) (μ : ℕ → ℤ)
    (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [n] μ (cbrtCeilTime n) fun r μ' => r = (cbrtLeast n : ℤ) ∧ μ' = μ := by sorry
