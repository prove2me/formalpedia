-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_yPhase_succ
-- name    : Lean4LPD.PauliString.yPhase_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:52.540828+00:00
-- url     : https://prove2.me/theorems/a7a9de06-3da2-493e-b39f-e73152285490
-- title:
--   Pauli String: y Phase succ
-- statement:
--   Head/tail decomposition of the Y-site phase, supporting `def:pauli_basis`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L121-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L121-L123

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.yPhase_succ {n : ℕ} (x z : Bits (n + 1)) :
    yPhase x z = ((x 0 * z 0).val : ZMod 4) + yPhase (Fin.tail x) (Fin.tail z) := by sorry
