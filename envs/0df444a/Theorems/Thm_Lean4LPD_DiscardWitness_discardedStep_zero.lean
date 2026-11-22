-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_discardedStep_zero
-- name    : Lean4LPD.DiscardWitness.discardedStep_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:30.090713+00:00
-- url     : https://prove2.me/theorems/57871893-9a42-4210-be8a-46c3b21209d7
-- title:
--   Discard Witness: discarded Step zero
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the named discarded-step
--   operator `X₁`, not only an independently written difference, is exactly `Q`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L257-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L257-L258

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.discardedStep_zero : discardedStep Gs angles 2 1 (toMatrix P) 0 = toMatrix Q := by sorry
