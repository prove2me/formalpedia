-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeff_toMatrix_herm
-- name    : Lean4LPD.PauliString.coeff_toMatrix_herm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:48.486881+00:00
-- url     : https://prove2.me/theorems/dab1550c-b473-4608-8126-d4f7a63227b1
-- title:
--   Pauli String: coeff to Matrix herm
-- statement:
--   **The coefficient vector of a basis Pauli is a unit vector.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L336-L345
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L336-L345

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

theorem Lean4LPD.PauliString.coeff_toMatrix_herm (p q : PauliIndex n) :
    coeff (toMatrix (herm q)) p = if p = q then 1 else 0 := by sorry
