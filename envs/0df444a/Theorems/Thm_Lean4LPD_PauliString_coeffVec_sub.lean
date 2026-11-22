-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeffVec_sub
-- name    : Lean4LPD.PauliString.coeffVec_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:43.548804+00:00
-- url     : https://prove2.me/theorems/51f78406-207d-4a20-86b9-c49ef5002904
-- title:
--   Pauli String: coeff Vec sub
-- statement:
--   Coefficient vectors preserve subtraction, so the operator difference of
--   `apd:eq:step_component` can be compared in coefficient space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L60-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L60-L64

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.coeffVec_sub (A B : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (A - B) = coeffVec A - coeffVec B := by sorry
