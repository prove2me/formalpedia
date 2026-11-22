-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_highSet_nonempty
-- name    : Lean4LPD.DiscardWitness.highSet_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:17.967799+00:00
-- url     : https://prove2.me/theorems/cfcf6c21-2053-4114-b80c-571453b97d91
-- title:
--   Discard Witness: high Set nonempty
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the high-weight sector at the
--   chosen cutoff is nonempty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L120-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L120-L121

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.highSet_nonempty : (highSet 2 1).Nonempty := by sorry
