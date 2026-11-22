-- Prove2me | Theorems.Thm_Lean4LPD_cZero_le_two
-- name    : Lean4LPD.cZero_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:09.150974+00:00
-- url     : https://prove2.me/theorems/bd501af5-871b-4c04-a4d9-e5cc469aab5c
-- title:
--   Lean4 LPD: c Zero le two
-- statement:
--   **`c₀ ≤ 2`** whenever `Admissible r m G`, `1 ≤ m`, `5 ≤ r` and `0 ≤ B ≤ 1`: the form in which
--   the constant enters the threshold `t₀` of `apd:thm:one_step_truncation_error`. It follows from
--   `cZero_le_two_sharp` and `√2 ≤ 1.4143`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L199-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L199-L205

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_le_two {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by sorry
