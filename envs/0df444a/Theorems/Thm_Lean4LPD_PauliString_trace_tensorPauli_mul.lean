-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_tensorPauli_mul
-- name    : Lean4LPD.PauliString.trace_tensorPauli_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:02.269874+00:00
-- url     : https://prove2.me/theorems/dcd17b4a-73c0-4278-8ad1-73cf50b544fe
-- title:
--   Pauli String: trace tensor Pauli mul
-- statement:
--   The Hermitian form of the positive tensor Pauli trace pairing in `def:pauli_basis`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L272-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L272-L278

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.trace_tensorPauli_mul {n : ℕ} (p q : PauliIndex n) :
    (tensorPauli n p.1 p.2 * tensorPauli n q.1 q.2).trace =
      if p = q then (2 : ℂ) ^ n else 0 := by sorry
