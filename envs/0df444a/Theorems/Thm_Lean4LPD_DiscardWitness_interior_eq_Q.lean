-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_interior_eq_Q
-- name    : Lean4LPD.DiscardWitness.interior_eq_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:41:06.934948+00:00
-- url     : https://prove2.me/theorems/16df12a6-dfb6-4cba-913e-0d1a6283f963
-- title:
--   Discard Witness: interior eq Q
-- statement:
--   Concrete regression example for `apd:thm:triangle`: the rotation-indexed trajectory still
--   contains `Q` inside the step, because the cutoff acts at the step boundary and not after every
--   rotation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L232-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L232-L234

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.interior_eq_Q : trotterTraj Gs angles 2 1 (toMatrix P) 1 = toMatrix Q := by sorry
