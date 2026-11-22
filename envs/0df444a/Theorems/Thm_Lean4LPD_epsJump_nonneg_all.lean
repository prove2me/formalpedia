-- Prove2me | Theorems.Thm_Lean4LPD_epsJump_nonneg_all
-- name    : Lean4LPD.epsJump_nonneg_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:01:23.340817+00:00
-- url     : https://prove2.me/theorems/2d695d1d-d05d-4d92-85ac-609769df4420
-- title:
--   Lean4 LPD: eps Jump nonneg all
-- statement:
--   The jump factors `ε_j^{(m)}` of `apd:rmk:multijump` are nonnegative for all indices. The
--   ladder recurrence only sums over `j ≥ 1`; the case `j = 0`, where the formula gives
--   `ε_0^{(m)} = 1`, is included because `MultiLadder.le_majorant` asks for nonnegativity at all
--   indices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerLadder.lean#L107-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerLadder.lean#L107-L111

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

theorem Lean4LPD.epsJump_nonneg_all {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (j m : ℕ) : 0 ≤ epsJump kh1 c a j m := by sorry
