-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_discardedStep_ne_zero
-- name    : Lean4LPD.DiscardWitness.discardedStep_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:32.48971+00:00
-- url     : https://prove2.me/theorems/d9e54919-85ed-4e2c-a3ae-631ddcd80d42
-- title:
--   Discard Witness: discarded Step ne zero
-- statement:
--   Concrete regression example for `apd:eq:step_component`: the algorithm's first discarded
--   operator is provably nonzero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L262-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L262-L264

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.discardedStep_ne_zero : discardedStep Gs angles 2 1 (toMatrix P) 0 ≠ 0 := by sorry
