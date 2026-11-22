-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_herm_P
-- name    : Lean4LPD.DiscardWitness.herm_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:03.470815+00:00
-- url     : https://prove2.me/theorems/0a74cab9-2e7f-404a-8e6d-136c09b272dd
-- title:
--   Discard Witness: herm P
-- statement:
--   Concrete regression helper for `apd:eq:step_component`: the input uses the canonical
--   Hermitian representative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L76-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L76-L76

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.herm_P : herm (cls P) = P := by sorry
