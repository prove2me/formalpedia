-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_cutoff_ne_univ
-- name    : Lean4LPD.DiscardWitness.cutoff_ne_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:02.709535+00:00
-- url     : https://prove2.me/theorems/eff7faee-9195-411b-93b9-fb69f90aa3d3
-- title:
--   Discard Witness: cutoff ne univ
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the retained set is a proper
--   subset of all Pauli classes, since it excludes the class of `Q`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L125-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L125-L129

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.cutoff_ne_univ : (highSet 2 1)ᶜ ≠ univ := by sorry
