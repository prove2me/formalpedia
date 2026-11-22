-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_truncOp
-- name    : Lean4LPD.PauliString.pauliNorm_truncOp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:21.855642+00:00
-- url     : https://prove2.me/theorems/c6bc5f95-c00a-4943-8421-4d4a1026d0c9
-- title:
--   Pauli String: pauli Norm trunc Op
-- statement:
--   A projected operator's Pauli norm is its restricted coefficient norm, the norm bridge used
--   for the discarded component in `apd:thm:triangle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L102-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L102-L104

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.pauliNorm_truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (truncOp S O) = ‖restr S (coeffVec O)‖ := by sorry
