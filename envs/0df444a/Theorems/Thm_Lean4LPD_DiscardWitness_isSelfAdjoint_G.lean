-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_isSelfAdjoint_G
-- name    : Lean4LPD.DiscardWitness.isSelfAdjoint_G
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:37.038562+00:00
-- url     : https://prove2.me/theorems/03d09348-788a-497a-872c-0854673ca659
-- title:
--   Discard Witness: is Self Adjoint G
-- statement:
--   Concrete regression data for `apd:eq:step_component`: `G` is Hermitian.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L55-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L55-L55

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.isSelfAdjoint_G : IsSelfAdjoint G := by sorry
