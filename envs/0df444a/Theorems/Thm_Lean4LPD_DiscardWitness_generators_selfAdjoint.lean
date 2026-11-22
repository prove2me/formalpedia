-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_generators_selfAdjoint
-- name    : Lean4LPD.DiscardWitness.generators_selfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:36.671871+00:00
-- url     : https://prove2.me/theorems/2f46d581-9fa2-40cd-8f13-53cd34515d03
-- title:
--   Discard Witness: generators self Adjoint
-- statement:
--   Concrete regression data for `apd:eq:step_component`: every generator is Hermitian.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L188-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L188-L192

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.generators_selfAdjoint (g : ℕ) : IsSelfAdjoint (Gs g) := by sorry
