-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sub_truncOp_compl
-- name    : Lean4LPD.PauliString.pauliNorm_sub_truncOp_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:45.229687+00:00
-- url     : https://prove2.me/theorems/5355663e-e8c5-4cf9-ad31-1854f67f77a7
-- title:
--   Pauli String: pauli Norm sub trunc Op compl
-- statement:
--   The norm of the operator discarded by retaining `Sᶜ` is the norm on `S`, the general-set
--   form of the final norm identification in `apd:thm:triangle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L115-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L115-L118

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

theorem Lean4LPD.PauliString.pauliNorm_sub_truncOp_compl (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (O - truncOp Sᶜ O) = ‖restr S (coeffVec O)‖ := by sorry
