-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_Q_highNorm
-- name    : Lean4LPD.DiscardWitness.Q_highNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:26.62264+00:00
-- url     : https://prove2.me/theorems/4745edaf-2a3e-4c41-af16-d7ef4bf6bba0
-- title:
--   Discard Witness: Q high Norm
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the high-weight scalar before
--   the cutoff is also exactly one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L174-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L174-L178

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.Q_highNorm : highNorm 1 (toMatrix Q) = 1 := by sorry
