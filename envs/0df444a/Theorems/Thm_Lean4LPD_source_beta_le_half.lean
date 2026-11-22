-- Prove2me | Theorems.Thm_Lean4LPD_source_beta_le_half
-- name    : Lean4LPD.source_beta_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:03:49.810803+00:00
-- url     : https://prove2.me/theorems/be7b56c9-85f5-4993-8e39-c344f0ed6957
-- title:
--   Lean4 LPD: source beta le half
-- statement:
--   In the paper's parameter regime, the same step-count condition gives `β ≤ 1/2`, the regime
--   of the entry-factor bound `entryFactor_le`
--   (`apd:eq:multijump_factor`; `apd:eq:entry_bound`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L109-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L109-L116

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD

theorem Lean4LPD.source_beta_le_half {kh1 c a A r : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hr : 0 < r) (haA : a ≤ A / r)
    (hsteps : 8 * (Real.exp 1) ^ 2 * rungW kh1 c 2 * A ≤ r) :
    betaOf kh1 c a ≤ 1 / 2 := by sorry
