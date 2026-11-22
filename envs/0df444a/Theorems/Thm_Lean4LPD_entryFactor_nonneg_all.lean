-- Prove2me | Theorems.Thm_Lean4LPD_entryFactor_nonneg_all
-- name    : Lean4LPD.entryFactor_nonneg_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:01:24.725278+00:00
-- url     : https://prove2.me/theorems/c2f80d5e-a26b-4940-abf4-b8a292c136cc
-- title:
--   Lean4 LPD: entry Factor nonneg all
-- statement:
--   The entry factors `E_m` of `apd:eq:composition_majorant` are nonnegative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerLadder.lean#L114-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerLadder.lean#L114-L116

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.entryFactor_nonneg_all {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (m : ℕ) : 0 ≤ entryFactor kh1 c a m := by sorry
