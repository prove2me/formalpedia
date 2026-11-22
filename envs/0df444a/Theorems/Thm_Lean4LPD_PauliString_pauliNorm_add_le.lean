-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_add_le
-- name    : Lean4LPD.PauliString.pauliNorm_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:41.439814+00:00
-- url     : https://prove2.me/theorems/9e4d498d-6358-48f4-8cd4-3e5ae5d033f8
-- title:
--   Pauli String: pauli Norm add le
-- statement:
--   Minkowski's inequality for the Pauli 2-norm, used on the operator telescope of
--   `apd:thm:triangle`. This is an inequality for the `ℓ²` norm of the coefficient vector, not for
--   the matrix operator norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L82-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L82-L84

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

theorem Lean4LPD.PauliString.pauliNorm_add_le (A B : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (A + B) ≤ pauliNorm A + pauliNorm B := by sorry
