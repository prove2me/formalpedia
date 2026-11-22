-- Prove2me | Theorems.Thm_Lean4LPD_DiscardWitness_phaseMul_G_P
-- name    : Lean4LPD.DiscardWitness.phaseMul_G_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:00.1768+00:00
-- url     : https://prove2.me/theorems/6435f014-d5a5-49e2-96f8-b6ce720341a6
-- title:
--   Discard Witness: phase Mul G P
-- statement:
--   Concrete regression helper for `apd:eq:step_component`: the first rotation's Hermitian
--   partner is exactly `Q`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L88-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean#L88-L88

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.DiscardWitness
open Finset PauliString

theorem Lean4LPD.DiscardWitness.phaseMul_G_P : phaseMul 1 (G * P) = Q := by sorry
