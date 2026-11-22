-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sub_truncOp
-- name    : Lean4LPD.PauliString.pauliNorm_sub_truncOp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:19.291169+00:00
-- url     : https://prove2.me/theorems/38adc258-2081-4fc9-acac-e9ac58f09c2b
-- title:
--   Pauli String: pauli Norm sub trunc Op
-- statement:
--   The norm of the operator discarded by retaining `S` is the norm on `Sᶜ`. This generalizes
--   the final norm identification of `apd:thm:triangle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L108-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L108-L111

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

theorem Lean4LPD.PauliString.pauliNorm_sub_truncOp (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (O - truncOp S O) = ‖restr Sᶜ (coeffVec O)‖ := by sorry
