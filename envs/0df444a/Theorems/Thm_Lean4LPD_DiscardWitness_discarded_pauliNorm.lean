-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_discarded_pauliNorm
-- name    : Lean4LPD.DiscardWitness.discarded_pauliNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:40.537143+00:00
-- url     : https://prove2.me/theorems/dc6e5cf0-e2ef-4b6b-9d08-657cfbf46228
-- title:
--   Discard Witness: discarded pauli Norm
-- statement:
--   Concrete regression example for `apd:thm:triangle`: the discarded norm, the scalar used
--   in the triangle bound's summand, is exactly one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L168-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L168-L170

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.discarded_pauliNorm :
    pauliNorm (toMatrix Q - truncOp (highSet 2 1)ᶜ (toMatrix Q)) = 1 := by sorry
