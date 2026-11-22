-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_weight_G
-- name    : Lean4LPD.DiscardWitness.weight_G
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:51.116258+00:00
-- url     : https://prove2.me/theorems/8348b109-b9e4-47c7-9dc9-6c8fc04061f7
-- title:
--   Discard Witness: weight G
-- statement:
--   Concrete regression data for `apd:eq:step_component`: `n = k_h = 2`, so the generator
--   is not one-local.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L65-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L65-L65

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.weight_G : weight G = 2 := by sorry
