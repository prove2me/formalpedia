-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_step_one
-- name    : Lean4LPD.DiscardWitness.step_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:24.450036+00:00
-- url     : https://prove2.me/theorems/48662c1d-a2f8-4ab8-a2c8-8e3be04aa12b
-- title:
--   Discard Witness: step one
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the independent full-step
--   recurrence removes the newly generated weight-two observable at the first step boundary.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L226-L227
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L226-L227

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.step_one : trotterStepTraj Gs angles 2 1 (toMatrix P) 1 = 0 := by sorry
