-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_coeffVec_sub_truncOp
-- name    : Lean4LPD.PauliString.coeffVec_sub_truncOp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:35.401146+00:00
-- url     : https://prove2.me/theorems/cc95912a-d6c6-4876-b4c0-cfa33737bf2e
-- title:
--   Pauli String: coeff Vec sub trunc Op
-- statement:
--   The coefficient vector of the discarded operator `O - Π_S O` is the coefficient vector of
--   `O` restricted to the complement `Sᶜ`; a coefficient-space form of `apd:eq:step_component`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L95-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L95-L98

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

theorem Lean4LPD.PauliString.coeffVec_sub_truncOp (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (O - truncOp S O) = restr Sᶜ (coeffVec O) := by sorry
