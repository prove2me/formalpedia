-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_cutoff_Q
-- name    : Lean4LPD.DiscardWitness.cutoff_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:38.961276+00:00
-- url     : https://prove2.me/theorems/92fadc0d-32c5-4269-b089-2bab70a84883
-- title:
--   Discard Witness: cutoff Q
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the cutoff removes the whole
--   new component, by its coefficients, not by an assumed operator identity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L133-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L133-L140

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.cutoff_Q : truncOp (highSet 2 1)ᶜ (toMatrix Q) = 0 := by sorry
