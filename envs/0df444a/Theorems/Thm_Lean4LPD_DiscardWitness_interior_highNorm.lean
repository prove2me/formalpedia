-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_interior_highNorm
-- name    : Lean4LPD.DiscardWitness.interior_highNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:20.465441+00:00
-- url     : https://prove2.me/theorems/e2660566-7dee-45ad-ab48-2a19a2287546
-- title:
--   Discard Witness: interior high Norm
-- statement:
--   Concrete regression example for `apd:thm:triangle`: the interior high-weight mass is
--   exactly one. This excludes a vacuous zero-sector witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L238-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L238-L239

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.interior_highNorm : highNorm 1 (trotterTraj Gs angles 2 1 (toMatrix P) 1) = 1 := by sorry
