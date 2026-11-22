-- Prove2me | Theorems.Thm_Lean4LPD_epsJump_diag_le_chainWeight
-- name    : Lean4LPD.epsJump_diag_le_chainWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:53.42137+00:00
-- url     : https://prove2.me/theorems/88a8064a-cc1a-4202-b483-46dc4fd24462
-- title:
--   Lean4 LPD: eps Jump diag le chain Weight
-- statement:
--   The first jump's leading term is bounded by its all-ones weight, including a zero angle.
--   Supporting theorem for `apd:eq:entry_bound` and `apd:eq:total_high_weight_norm`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L164-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L164-L167

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.epsJump_diag_le_chainWeight {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    epsJump kh1 c a m m ≤ (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by sorry
