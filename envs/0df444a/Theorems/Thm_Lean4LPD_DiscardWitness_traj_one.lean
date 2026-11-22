-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_traj_one
-- name    : Lean4LPD.DiscardWitness.traj_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:44.655645+00:00
-- url     : https://prove2.me/theorems/0e002066-c374-481e-9c63-ccc21dbe7ba1
-- title:
--   Discard Witness: traj one
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the first rotation creates
--   weight-two mass in the actual recursive, untruncated trajectory.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L204-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L204-L206

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.traj_one : traj Gs angles (toMatrix P) 1 = toMatrix Q := by sorry
