-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_input_local
-- name    : Lean4LPD.DiscardWitness.input_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:39.676804+00:00
-- url     : https://prove2.me/theorems/80e504b7-fa8a-49df-880f-7ec0cb3d766b
-- title:
--   Discard Witness: input local
-- statement:
--   Concrete regression example for `apd:eq:step_component`: input locality is genuinely
--   `k_o = 1`, not `k_o = n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L95-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L95-L97

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.input_local (p : PauliIndex 2) (hp : 1 < wt p) : coeff (toMatrix P) p = 0 := by sorry
