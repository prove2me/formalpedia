-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_restr_le
-- name    : Lean4LPD.PauliString.norm_restr_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:40.059912+00:00
-- url     : https://prove2.me/theorems/b5ddb5b5-6a75-40b4-81de-a6b8c9fe76ab
-- title:
--   Pauli String: norm restr le
-- statement:
--   Dropping classes cannot increase the `ℓ²` mass.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L395-L401
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L395-L401

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.norm_restr_le (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr S y‖ ≤ ‖y‖ := by sorry
