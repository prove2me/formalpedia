-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_second_rotation
-- name    : Lean4LPD.DiscardWitness.second_rotation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:37.441854+00:00
-- url     : https://prove2.me/theorems/c424dfa1-5353-4200-9d40-0916f98c99e7
-- title:
--   Discard Witness: second rotation
-- statement:
--   Concrete regression example for `apd:eq:step_component`: a genuine second rotation
--   preserves the high-weight component until the step boundary.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L114-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L114-L116

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.second_rotation (θ : ℝ) :
    rot (toMatrix Q) θ * toMatrix Q * rot (toMatrix Q) (-θ) = toMatrix Q := by sorry
