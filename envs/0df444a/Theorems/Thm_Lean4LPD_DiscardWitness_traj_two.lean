-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_traj_two
-- name    : Lean4LPD.DiscardWitness.traj_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:16.708344+00:00
-- url     : https://prove2.me/theorems/2ed62077-9573-4c11-97f6-17ba1d2cbcab
-- title:
--   Discard Witness: traj two
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the two-rotation evolution
--   still contains exactly `Q` immediately before its end-of-step cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L210-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L210-L212

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.traj_two : traj Gs angles (toMatrix P) 2 = toMatrix Q := by sorry
