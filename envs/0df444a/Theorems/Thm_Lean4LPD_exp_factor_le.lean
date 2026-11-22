-- Prove2me | Theorems.Thm_Lean4LPD_exp_factor_le
-- name    : Lean4LPD.exp_factor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:49.246028+00:00
-- url     : https://prove2.me/theorems/37e28fa7-35f8-47dd-bdcd-6deedb1cd4ae
-- title:
--   Lean4 LPD: exp factor le
-- statement:
--   The exponential factor of `c₀` is at most `64/55` when `Admissible r m G` and `1 ≤ m`:
--   `r·Γ ≥ 8(m*+1)²` bounds the exponent by `9/(32(m*+1)) ≤ 9/64`, and `exp (9/64) ≤ 1/(1 − 9/64)` by
--   `exp_le_one_div_one_sub`. The clause `m ≤ r` of `Admissible` is not used, and no lower bound on `r`
--   beyond `1 ≤ r` is needed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L137-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L137-L147

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.exp_factor_le {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) :
    exp (9 / 4 * (m + 1) / (r * G)) ≤ 64 / 55 := by sorry
