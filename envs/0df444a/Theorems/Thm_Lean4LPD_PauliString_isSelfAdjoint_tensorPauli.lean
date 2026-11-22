-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_tensorPauli
-- name    : Lean4LPD.PauliString.isSelfAdjoint_tensorPauli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:52.973598+00:00
-- url     : https://prove2.me/theorems/ae931b94-5a18-4fb5-922b-f3ab4ef5278f
-- title:
--   Pauli String: is Self Adjoint tensor Pauli
-- statement:
--   The literal tensor Pauli is self-adjoint, as required by `def:pauli_basis`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L252-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L252-L255

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.isSelfAdjoint_tensorPauli {n : ℕ} (p : PauliIndex n) :
    IsSelfAdjoint (tensorPauli n p.1 p.2) := by sorry
