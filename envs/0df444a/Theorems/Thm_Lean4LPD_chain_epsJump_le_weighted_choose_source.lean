-- Prove2me | Theorems.Thm_Lean4LPD_chain_epsJump_le_weighted_choose_source
-- name    : Lean4LPD.chain_epsJump_le_weighted_choose_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:11.689134+00:00
-- url     : https://prove2.me/theorems/322ad709-5b09-4aaf-8cf9-0bab3170a15b
-- title:
--   Lean4 LPD: chain eps Jump le weighted choose source
-- statement:
--   The same concrete chain bound with the paper's entry factor `1 + 4eβ`, suitable for
--   direct composition with `apd:eq:total_high_weight_norm`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L254-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L254-L265

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.chain_epsJump_le_weighted_choose_source {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) (k m : ℕ) (hm : 1 ≤ m) :
    chain (epsJump kh1 c a) (entryFactor kh1 c a) (k + 1) m
      ≤ (1 + 4 * Real.exp 1 * betaOf kh1 c a) * (9 / 4 : ℝ) ^ (m - (k + 1))
        * chainWeight kh1 c a m * ((m - 1).choose k : ℝ) := by sorry
