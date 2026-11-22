-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_weight_P
-- name    : Lean4LPD.DiscardWitness.weight_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:58.538613+00:00
-- url     : https://prove2.me/theorems/5af4c582-ce44-4f14-bd16-64133e3ed921
-- title:
--   Discard Witness: weight P
-- statement:
--   Concrete regression data for `apd:eq:step_component`: `k_o = 1 < n = 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L68-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L68-L68

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.weight_P : weight P = 1 := by sorry
