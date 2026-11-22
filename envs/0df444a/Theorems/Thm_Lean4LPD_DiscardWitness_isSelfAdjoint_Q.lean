-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_isSelfAdjoint_Q
-- name    : Lean4LPD.DiscardWitness.isSelfAdjoint_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:26.296261+00:00
-- url     : https://prove2.me/theorems/db6560f9-64ab-4810-aaba-190617451f4b
-- title:
--   Discard Witness: is Self Adjoint Q
-- statement:
--   Concrete regression data for `apd:eq:step_component`: the new component is Hermitian.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L61-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L61-L61

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.isSelfAdjoint_Q : IsSelfAdjoint Q := by sorry
