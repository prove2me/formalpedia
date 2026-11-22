-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_boundary_eq_zero
-- name    : Lean4LPD.DiscardWitness.boundary_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:22.513496+00:00
-- url     : https://prove2.me/theorems/675cc2e2-e46b-4940-a605-eca862a96ea0
-- title:
--   Discard Witness: boundary eq zero
-- statement:
--   Concrete regression example for `apd:eq:step_component`: after the second rotation,
--   the rotation-indexed execution agrees with the independently computed step cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L243-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L243-L245

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.boundary_eq_zero : trotterTraj Gs angles 2 1 (toMatrix P) 2 = 0 := by sorry
