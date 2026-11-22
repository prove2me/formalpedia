-- Prove2me | Theorems.Thm_Lean4LPD_factorial_ratio_le_pow
-- name    : Lean4LPD.factorial_ratio_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:00.539465+00:00
-- url     : https://prove2.me/theorems/9be7f9d3-f64a-4b62-8d36-e846c284da81
-- title:
--   Lean4 LPD: factorial ratio le pow
-- statement:
--   The factorial-ratio estimate `m!/(m-D)! ≤ m^D` used in `apd:eq:total_high_weight_norm`,
--   proved through the falling factorial.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L161-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L161-L171

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.factorial_ratio_le_pow {m D : ℕ} (hD : D ≤ m) :
    (Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ) ≤ (m : ℝ) ^ D := by sorry
