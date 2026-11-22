-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_input_highNorm
-- name    : Lean4LPD.DiscardWitness.input_highNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:16.349116+00:00
-- url     : https://prove2.me/theorems/eb035600-3cc8-4cf4-8517-ea4063f6b5c3
-- title:
--   Discard Witness: input high Norm
-- statement:
--   Concrete regression example for `apd:eq:step_component`: no high-weight mass is present
--   initially; the later discarded mass must be produced by the rotation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L101-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L101-L101

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.input_highNorm : highNorm 1 (toMatrix P) = 0 := by sorry
