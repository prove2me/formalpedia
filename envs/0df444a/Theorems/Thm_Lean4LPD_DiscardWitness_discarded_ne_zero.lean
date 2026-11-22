-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_discarded_ne_zero
-- name    : Lean4LPD.DiscardWitness.discarded_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:24.652637+00:00
-- url     : https://prove2.me/theorems/20d5d8ba-ef55-4035-93d9-7517cb4d5815
-- title:
--   Discard Witness: discarded ne zero
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the discarded operator is
--   provably nonzero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L150-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L150-L152

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.discarded_ne_zero : toMatrix Q - truncOp (highSet 2 1)ᶜ (toMatrix Q) ≠ 0 := by sorry
