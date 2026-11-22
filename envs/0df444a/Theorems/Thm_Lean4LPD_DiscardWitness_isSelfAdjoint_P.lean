-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_isSelfAdjoint_P
-- name    : Lean4LPD.DiscardWitness.isSelfAdjoint_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:56.359442+00:00
-- url     : https://prove2.me/theorems/543dfde4-068d-40a4-b16e-e1c45adb1958
-- title:
--   Discard Witness: is Self Adjoint P
-- statement:
--   Concrete regression data for `apd:eq:step_component`: the input is Hermitian.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L58-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L58-L58

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.isSelfAdjoint_P : IsSelfAdjoint P := by sorry
