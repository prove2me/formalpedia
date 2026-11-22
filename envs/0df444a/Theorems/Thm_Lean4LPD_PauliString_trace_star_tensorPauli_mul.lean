-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_star_tensorPauli_mul
-- name    : Lean4LPD.PauliString.trace_star_tensorPauli_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:56.936798+00:00
-- url     : https://prove2.me/theorems/5c00d370-2fb1-4378-abfb-9f2abc617223
-- title:
--   Pauli String: trace star tensor Pauli mul
-- statement:
--   Orthogonality of the positive tensor Pauli family, in the unnormalized convention of
--   `def:pauli_basis`. The normalized statement divides this pairing by `2^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L259-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L259-L269

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.trace_star_tensorPauli_mul {n : ℕ} (p q : PauliIndex n) :
    (star (tensorPauli n p.1 p.2) * tensorPauli n q.1 q.2).trace =
      if p = q then (2 : ℂ) ^ n else 0 := by sorry
