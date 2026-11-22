-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_schedule_one
-- name    : Lean4LPD.DiscardWitness.schedule_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:36.226126+00:00
-- url     : https://prove2.me/theorems/d8eac0d1-e05d-4e64-a992-0b36fc105ade
-- title:
--   Discard Witness: schedule one
-- statement:
--   Concrete regression example for `apd:thm:triangle`: the second rotation is followed by
--   the genuine weight-one cutoff, at the end of the step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L221-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L221-L222

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.schedule_one : trotterSchedule (n := 2) 2 1 1 = (highSet 2 1)ᶜ := by sorry
