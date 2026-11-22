-- Prove2me | Theorems.Thm_Lean4LPD_betaOf_nonneg_for_chain
-- name    : Lean4LPD.betaOf_nonneg_for_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:22.303973+00:00
-- url     : https://prove2.me/theorems/52cb431a-ad56-4f5f-aadc-31d5cd3322ac
-- title:
--   Lean4 LPD: beta Of nonneg for chain
-- statement:
--   The concrete expansion parameter is nonnegative. Supporting sign check for
--   `apd:eq:entry_bound`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L171-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L171-L175

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.betaOf_nonneg_for_chain {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) : 0 ≤ betaOf kh1 c a := by sorry
