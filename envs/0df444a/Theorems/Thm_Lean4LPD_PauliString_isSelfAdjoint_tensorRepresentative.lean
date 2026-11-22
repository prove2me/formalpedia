-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_tensorRepresentative
-- name    : Lean4LPD.PauliString.isSelfAdjoint_tensorRepresentative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:50.207009+00:00
-- url     : https://prove2.me/theorems/c8b60557-bda9-4a4a-8f5c-bf68afad93ad
-- title:
--   Pauli String: is Self Adjoint tensor Representative
-- statement:
--   Positive tensor representatives are genuine Hermitian Pauli strings, not just tensors
--   identified up to a freely chosen phase (`def:pauli_basis`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L241-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L241-L244

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.isSelfAdjoint_tensorRepresentative {n : ℕ} (p : PauliIndex n) :
    IsSelfAdjoint (tensorRepresentative p) := by sorry
