-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_split
-- name    : Lean4LPD.PauliString.toMatrix_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:09.40016+00:00
-- url     : https://prove2.me/theorems/2e350d2b-c250-46bb-8616-5a4a3c341932
-- title:
--   Pauli String: to Matrix split
-- statement:
--   The entrywise model factors into a one-qubit X^x Z^z entry and its tail. This is the
--   algebraic step relating `toMatrix` to `def:pauli_basis`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L148-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L148-L172

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.toMatrix_split {n : ℕ} (s : PauliString (n + 1)) (a b : Bits (n + 1)) :
    toMatrix s a b = qubitXZ (s.x 0) (s.z 0) (a 0) (b 0) *
      toMatrix (dropFirst s) (Fin.tail a) (Fin.tail b) := by sorry
