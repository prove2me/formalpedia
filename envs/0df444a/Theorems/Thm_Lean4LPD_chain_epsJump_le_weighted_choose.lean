-- Prove2me | Theorems.Thm_Lean4LPD_chain_epsJump_le_weighted_choose
-- name    : Lean4LPD.chain_epsJump_le_weighted_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:03.895484+00:00
-- url     : https://prove2.me/theorems/3075c9cd-8297-4d5b-8140-cacdf0c4b123
-- title:
--   Lean4 LPD: chain eps Jump le weighted choose
-- statement:
--   **Concrete chain-product/composition-count bound, with all local and entry premises
--   discharged.** The overshoot inflation occurs exactly once, not once per composition part.
--   This is the chain-weight step of `apd:eq:total_high_weight_norm`, with the entry factor
--   `1 + 2β`, which is stronger than the paper's statement. It remains valid at zero angle.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L239-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L239-L250

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.chain_epsJump_le_weighted_choose {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) (k m : ℕ) (hm : 1 ≤ m) :
    chain (epsJump kh1 c a) (entryFactor kh1 c a) (k + 1) m
      ≤ (1 + 2 * betaOf kh1 c a) * (9 / 4 : ℝ) ^ (m - (k + 1))
        * chainWeight kh1 c a m * ((m - 1).choose k : ℝ) := by sorry
