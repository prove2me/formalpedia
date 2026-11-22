-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_eq_phase_tensor
-- name    : Lean4LPD.PauliString.toMatrix_eq_phase_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:29.038797+00:00
-- url     : https://prove2.me/theorems/9858656a-34c5-46c4-abe7-dfe40b31c762
-- title:
--   Pauli String: to Matrix eq phase tensor
-- statement:
--   **The matrix model is the phase-corrected tensor product of Pauli matrices.** For every
--   Pauli string `s`, `toMatrix s` is `i ^ (s.phase - yPhase s.x s.z)` times the Kronecker product
--   of the one-qubit Pauli matrices of `def:pauli_basis`. The identification of the entrywise model
--   with a tensor product is thus a theorem, not an assumption.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L178-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L178-L210

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.toMatrix_eq_phase_tensor : ∀ {n : ℕ} (s : PauliString n),
    toMatrix s = iPow (s.phase - yPhase s.x s.z) • tensorPauli n s.x s.z := by sorry
