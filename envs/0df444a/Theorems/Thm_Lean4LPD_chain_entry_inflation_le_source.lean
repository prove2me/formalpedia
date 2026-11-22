-- Prove2me | Theorems.Thm_Lean4LPD_chain_entry_inflation_le_source
-- name    : Lean4LPD.chain_entry_inflation_le_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:51.115967+00:00
-- url     : https://prove2.me/theorems/cc30edeb-7e29-46e1-a649-860d6cf68140
-- title:
--   Lean4 LPD: chain entry inflation le source
-- statement:
--   The entry inflation `1 + 2β` proved here is no larger than the paper's `1 + 4eβ`, because
--   `2 ≤ 4e` and `β ≥ 0`. Supporting comparison for `apd:eq:entry_bound` and
--   `apd:eq:total_high_weight_norm`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L213-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L213-L220

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.chain_entry_inflation_le_source {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    1 + 2 * betaOf kh1 c a ≤ 1 + 4 * Real.exp 1 * betaOf kh1 c a := by sorry
