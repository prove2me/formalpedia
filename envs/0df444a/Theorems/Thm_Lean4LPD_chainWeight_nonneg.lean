-- Prove2me | Theorems.Thm_Lean4LPD_chainWeight_nonneg
-- name    : Lean4LPD.chainWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:25.663938+00:00
-- url     : https://prove2.me/theorems/f356fb2a-1af0-4f55-81a6-24be0d10d6c9
-- title:
--   Lean4 LPD: chain Weight nonneg
-- statement:
--   All-ones weights are nonnegative for the physical nonnegative angle parameter.
--   Supporting lemma for `apd:eq:total_high_weight_norm`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L62-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L62-L65

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.chainWeight_nonneg {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (m : ℕ) : 0 ≤ chainWeight kh1 c a m := by sorry
