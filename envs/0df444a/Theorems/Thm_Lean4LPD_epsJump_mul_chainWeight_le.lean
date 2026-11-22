-- Prove2me | Theorems.Thm_Lean4LPD_epsJump_mul_chainWeight_le
-- name    : Lean4LPD.epsJump_mul_chainWeight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:21.905703+00:00
-- url     : https://prove2.me/theorems/f94583c0-e8dc-4642-ace8-c654a6c21729
-- title:
--   Lean4 LPD: eps Jump mul chain Weight le
-- statement:
--   **Every concrete internal jump satisfies the local chain-weight estimate.**
--   This discharges the ratio premise in the composition count of
--   `apd:eq:total_high_weight_norm`, with `j=m` retained for the entry estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L152-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L152-L160

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.epsJump_mul_chainWeight_le {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    epsJump kh1 c a j m * chainWeight kh1 c a (m - j)
      ≤ (9 / 4 : ℝ) ^ (j - 1) * chainWeight kh1 c a m := by sorry
