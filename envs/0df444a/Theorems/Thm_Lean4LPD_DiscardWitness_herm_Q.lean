-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_herm_Q
-- name    : Lean4LPD.DiscardWitness.herm_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:13.272822+00:00
-- url     : https://prove2.me/theorems/0e20df2c-a03e-4f00-9f2e-c2ad8b9adece
-- title:
--   Discard Witness: herm Q
-- statement:
--   Concrete regression helper for `apd:eq:step_component`: the created Pauli uses the canonical
--   Hermitian representative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L80-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L80-L80

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.herm_Q : herm (cls Q) = Q := by sorry
