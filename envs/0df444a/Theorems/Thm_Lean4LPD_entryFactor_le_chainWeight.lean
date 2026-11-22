-- Prove2me | Theorems.Thm_Lean4LPD_entryFactor_le_chainWeight
-- name    : Lean4LPD.entryFactor_le_chainWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:07.05879+00:00
-- url     : https://prove2.me/theorems/4e58f023-6462-4e09-bcaf-01663b67ffc1
-- title:
--   Lean4 LPD: entry Factor le chain Weight
-- statement:
--   **The concrete entry estimate charges the overshoot factor once.**
--   Combines `apd:eq:entry_bound`, in the stronger form `1 + 2β` proved as `entryFactor_le`,
--   with `apd:eq:part_factor`, as used in `apd:eq:composition_majorant`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L180-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L180-L194

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.entryFactor_le_chainWeight {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    entryFactor kh1 c a m
      ≤ (1 + 2 * betaOf kh1 c a) * (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by sorry
