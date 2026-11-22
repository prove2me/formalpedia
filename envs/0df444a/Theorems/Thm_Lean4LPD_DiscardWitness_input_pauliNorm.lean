-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_input_pauliNorm
-- name    : Lean4LPD.DiscardWitness.input_pauliNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:43:40.744069+00:00
-- url     : https://prove2.me/theorems/ba90286e-bf78-44c6-89af-13c252dc38ab
-- title:
--   Discard Witness: input pauli Norm
-- statement:
--   Concrete regression helper for `apd:thm:triangle`: the normalized Pauli norm of the input
--   is exactly one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L156-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L156-L158

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.input_pauliNorm : pauliNorm (toMatrix P) = 1 := by sorry
