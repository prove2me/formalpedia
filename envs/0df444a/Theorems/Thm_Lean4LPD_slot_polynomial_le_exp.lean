-- Prove2me | Theorems.Thm_Lean4LPD_slot_polynomial_le_exp
-- name    : Lean4LPD.slot_polynomial_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:08.247955+00:00
-- url     : https://prove2.me/theorems/9a2508a9-2ed1-4a10-a725-f46419da9d88
-- title:
--   Lean4 LPD: slot polynomial le exp
-- statement:
--   The complete factorial/slot `D`-sector estimate in `apd:eq:total_high_weight_norm`,
--   generalized from `9/4` to any nonnegative part-ratio bound `R`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L218-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L218-L226

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

theorem Lean4LPD.slot_polynomial_le_exp {m : ℕ} (hm : 1 ≤ m) {X R : ℝ} (hX : 0 < X) (hR : 0 ≤ R) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      R ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) ≤
      X ^ m / (Nat.factorial m : ℝ) * Real.exp (R * (m : ℝ) ^ 2 / X) := by sorry
