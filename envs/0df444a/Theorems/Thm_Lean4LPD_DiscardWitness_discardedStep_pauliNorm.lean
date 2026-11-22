-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_discardedStep_pauliNorm
-- name    : Lean4LPD.DiscardWitness.discardedStep_pauliNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:45.921494+00:00
-- url     : https://prove2.me/theorems/772067c6-8455-4f1d-88ce-d9c6b0310437
-- title:
--   Discard Witness: discarded Step pauli Norm
-- statement:
--   Concrete regression example for `apd:thm:triangle`: the generic discarded-operator norm
--   bridge computes the first error summand as exactly one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L268-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L268-L269

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.discardedStep_pauliNorm : pauliNorm (discardedStep Gs angles 2 1 (toMatrix P) 0) = 1 := by sorry
