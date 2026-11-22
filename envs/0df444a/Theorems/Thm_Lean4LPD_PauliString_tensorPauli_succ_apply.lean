-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_tensorPauli_succ_apply
-- name    : Lean4LPD.PauliString.tensorPauli_succ_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:24.784022+00:00
-- url     : https://prove2.me/theorems/c6d74ca4-d321-4ba3-a8bd-0562123de0ec
-- title:
--   Pauli String: tensor Pauli succ apply
-- statement:
--   The bit-indexed tensor product acts by the local matrix entry times its tail entry,
--   as required by `def:pauli_basis`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L136-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L136-L139

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.tensorPauli_succ_apply {n : ℕ} (x z a b : Bits (n + 1)) :
    tensorPauli (n + 1) x z a b =
      qubitPauli (x 0) (z 0) (a 0) (b 0) *
        tensorPauli n (Fin.tail x) (Fin.tail z) (Fin.tail a) (Fin.tail b) := by sorry
