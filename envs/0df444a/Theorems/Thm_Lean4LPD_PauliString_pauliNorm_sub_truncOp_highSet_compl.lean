-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sub_truncOp_highSet_compl
-- name    : Lean4LPD.PauliString.pauliNorm_sub_truncOp_highSet_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:29.838884+00:00
-- url     : https://prove2.me/theorems/a7acd2e2-3969-4756-bf76-bcade763c14b
-- title:
--   Pauli String: pauli Norm sub trunc Op high Set compl
-- statement:
--   **The high-weight scalar is the norm of the discarded operator.** Retaining the classes of
--   weight at most `w` discards an operator whose Pauli norm is exactly `highNorm w O`. This connects
--   the component `Õ^{(d)}_{≥w*+1}` of `apd:eq:step_component` with the high-weight norm
--   `apd:eq:def_high_weight_norm` that the ladder bounds (the identification of the truncated mass at
--   the start of the proof of `apd:thm:one_step_truncation_error`), and it holds for an arbitrary
--   operator `O`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L132-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L132-L134

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

theorem Lean4LPD.PauliString.pauliNorm_sub_truncOp_highSet_compl (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (O - truncOp (highSet n w)ᶜ O) = highNorm w O := by sorry
