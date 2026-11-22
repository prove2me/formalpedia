-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_schedule_zero
-- name    : Lean4LPD.DiscardWitness.schedule_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:18.963346+00:00
-- url     : https://prove2.me/theorems/3147d48e-325f-4e76-a7c6-65cb95af9c35
-- title:
--   Discard Witness: schedule zero
-- statement:
--   Concrete regression example for `apd:thm:triangle`: the first rotation of the length-two
--   step is not followed by a cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L216-L217
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L216-L217

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.schedule_zero : trotterSchedule (n := 2) 2 1 0 = univ := by sorry
