-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_discarded_eq_Q
-- name    : Lean4LPD.DiscardWitness.discarded_eq_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:59.329077+00:00
-- url     : https://prove2.me/theorems/d659aa3d-19a2-4cfd-94b8-c2dbcde18040
-- title:
--   Discard Witness: discarded eq Q
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the discarded operator is `Q`.
--   This is the subtraction defining the paper's `Õ^{(d)}_{≥w*+1}`, specialized to the evolved
--   witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L145-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L145-L146

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.discarded_eq_Q : toMatrix Q - truncOp (highSet 2 1)ᶜ (toMatrix Q) = toMatrix Q := by sorry
