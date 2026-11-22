-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeffVec_add
-- name    : Lean4LPD.PauliString.coeffVec_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:17.168496+00:00
-- url     : https://prove2.me/theorems/044482db-f198-48e1-9f4b-0ddcf52eb2ea
-- title:
--   Pauli String: coeff Vec add
-- statement:
--   Coefficient vectors preserve addition, allowing the Pauli-norm form of the triangle step
--   in `apd:thm:triangle` without choosing a norm instance on matrices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L65-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L65-L69

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.coeffVec_add (A B : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (A + B) = coeffVec A + coeffVec B := by sorry
