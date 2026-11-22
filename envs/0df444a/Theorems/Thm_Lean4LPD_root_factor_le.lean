-- Prove2me | Theorems.Thm_Lean4LPD_root_factor_le
-- name    : Lean4LPD.root_factor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:40.325521+00:00
-- url     : https://prove2.me/theorems/3ad39616-8293-43d8-a937-8f67b5fd7320
-- title:
--   Lean4 LPD: root factor le
-- statement:
--   The root factor of `c₀` is at most `√2` once `m* ≥ 1` and `0 ≤ B ≤ 1`. The hypothesis `1 ≤ m`
--   is exactly what halves the exponent; at `m = 0` the factor is the whole of `1 + B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L151-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L151-L163

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.root_factor_le {m B : ℝ} (hm : 1 ≤ m) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ Real.sqrt 2 := by sorry
