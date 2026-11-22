-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_toMatrix_tensorRepresentative
-- name    : Lean4LPD.PauliString.toMatrix_tensorRepresentative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:48.174994+00:00
-- url     : https://prove2.me/theorems/9faf0da3-4886-4189-9165-d4749c886dde
-- title:
--   Pauli String: to Matrix tensor Representative
-- statement:
--   The matrix of the positive tensor representative is exactly the tensor product of Pauli
--   matrices of `def:pauli_basis`, with no residual sign or phase.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L219-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L219-L222

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.toMatrix_tensorRepresentative {n : ℕ} (p : PauliIndex n) :
    toMatrix (tensorRepresentative p) = tensorPauli n p.1 p.2 := by sorry
