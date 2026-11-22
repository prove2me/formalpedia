-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_discardedStep_pauliNorm_pos
-- name    : Lean4LPD.DiscardWitness.discardedStep_pauliNorm_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:45:17.924335+00:00
-- url     : https://prove2.me/theorems/652cec01-50d7-4c63-a8d3-9e38b4d72cff
-- title:
--   Discard Witness: discarded Step pauli Norm pos
-- statement:
--   Concrete regression example for `apd:thm:triangle`: the first discarded norm is strictly
--   positive, unlike the high-weight norm of the retained boundary state.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L273-L276
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L273-L276

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.discardedStep_pauliNorm_pos :
    0 < pauliNorm (discardedStep Gs angles 2 1 (toMatrix P) 0) := by sorry
