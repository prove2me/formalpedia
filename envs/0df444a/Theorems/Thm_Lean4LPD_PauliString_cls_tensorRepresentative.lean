-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_cls_tensorRepresentative
-- name    : Lean4LPD.PauliString.cls_tensorRepresentative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:53.800803+00:00
-- url     : https://prove2.me/theorems/a8dae085-4e01-42c1-8d07-54c38ec87089
-- title:
--   Pauli String: cls tensor Representative
-- statement:
--   The positive tensor representative has the intended signless class
--   (`def:pauli_basis`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L248-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L248-L249

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.cls_tensorRepresentative {n : ℕ} (p : PauliIndex n) :
    cls (tensorRepresentative p) = p := by sorry

attribute [defeq] Lean4LPD.PauliString.cls_tensorRepresentative
