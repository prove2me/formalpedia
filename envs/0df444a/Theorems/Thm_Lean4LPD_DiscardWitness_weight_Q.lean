-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_weight_Q
-- name    : Lean4LPD.DiscardWitness.weight_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:31.38732+00:00
-- url     : https://prove2.me/theorems/de5eb6f6-c107-4f2c-84f1-01f5d648807b
-- title:
--   Discard Witness: weight Q
-- statement:
--   Concrete regression data for `apd:eq:step_component`: the created Pauli lies strictly
--   above `w* = 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L72-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L72-L72

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.weight_Q : weight Q = 2 := by sorry
