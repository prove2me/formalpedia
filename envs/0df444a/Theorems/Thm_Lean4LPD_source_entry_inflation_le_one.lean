-- Prove2me | Theorems.Thm_Lean4LPD_source_entry_inflation_le_one
-- name    : Lean4LPD.source_entry_inflation_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:02:41.475983+00:00
-- url     : https://prove2.me/theorems/b5cb34bd-4dcf-47d1-a7be-47e9ac195f49
-- title:
--   Lean4 LPD: source entry inflation le one
-- statement:
--   In the paper's parameter regime, the step-count condition `r ≥ 8e² w₂ A` together with
--   `a ≤ A / r` gives `B = 4eβ ≤ 1`, where `β = 2e w₂ a` (`apd:eq:multijump_factor`; `apd:eq:c0`;
--   `apd:thm:one_step_truncation_error`). This is the hypothesis `B ≤ 1` of `cZero_le_two`. The
--   proof multiplies through by `r`; no division by `a` occurs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L88-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerError.lean#L88-L104

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD

theorem Lean4LPD.source_entry_inflation_le_one {kh1 c a A r : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (hr : 0 < r) (haA : a ≤ A / r)
    (hsteps : 8 * (Real.exp 1) ^ 2 * rungW kh1 c 2 * A ≤ r) :
    4 * Real.exp 1 * betaOf kh1 c a ≤ 1 := by sorry
