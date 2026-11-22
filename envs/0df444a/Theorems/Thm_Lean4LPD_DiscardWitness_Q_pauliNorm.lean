-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_Q_pauliNorm
-- name    : Lean4LPD.DiscardWitness.Q_pauliNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:41:11.416597+00:00
-- url     : https://prove2.me/theorems/68a148af-2465-4729-8047-4f7359cdcd6c
-- title:
--   Discard Witness: Q pauli Norm
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the produced Pauli has exact
--   normalized norm one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L162-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L162-L164

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.Q_pauliNorm : pauliNorm (toMatrix Q) = 1 := by sorry
