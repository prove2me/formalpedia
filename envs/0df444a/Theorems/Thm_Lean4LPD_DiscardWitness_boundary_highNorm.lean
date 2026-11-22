-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_boundary_highNorm
-- name    : Lean4LPD.DiscardWitness.boundary_highNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:25.770914+00:00
-- url     : https://prove2.me/theorems/6578a97d-c3c4-4e2c-90bb-82a77f30aad9
-- title:
--   Discard Witness: boundary high Norm
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the kept high-weight mass is
--   zero at the boundary, in contrast to the positive mass discarded at that same boundary.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L249-L253
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L249-L253

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.boundary_highNorm : highNorm 1 (trotterTraj Gs angles 2 1 (toMatrix P) 2) = 0 := by sorry
