-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_first_rotation
-- name    : Lean4LPD.DiscardWitness.first_rotation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:33.881097+00:00
-- url     : https://prove2.me/theorems/5cbad83a-d8e1-4a15-891d-6438348f27e4
-- title:
--   Discard Witness: first rotation
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the first rotation creates
--   exactly one unit-amplitude weight-two Pauli, not a merely reachable branch.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L105-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L105-L110

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.first_rotation :
    rot (toMatrix G) (Real.pi / 2) * toMatrix P * rot (toMatrix G) (-(Real.pi / 2))
      = toMatrix Q := by sorry
