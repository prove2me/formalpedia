-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_sympForm_G_P
-- name    : Lean4LPD.DiscardWitness.sympForm_G_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:26.816806+00:00
-- url     : https://prove2.me/theorems/6c9ffd90-1e45-44b3-adf1-63ff652788fb
-- title:
--   Discard Witness: symp Form G P
-- statement:
--   Concrete regression helper for `apd:eq:step_component`: the first generator anticommutes
--   with the input.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L84-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L84-L84

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.sympForm_G_P : sympForm G P = 1 := by sorry
