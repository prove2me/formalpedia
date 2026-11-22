-- Prove2me | Theorems.Thm_Lean4LPD_entryFactor_le_chainWeight_source
-- name    : Lean4LPD.entryFactor_le_chainWeight_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:02.242163+00:00
-- url     : https://prove2.me/theorems/63d29796-3b73-4390-9b99-dc73a687f528
-- title:
--   Lean4 LPD: entry Factor le chain Weight source
-- statement:
--   The concrete entry premise with the paper's constant `1 + 4eβ`, still charged once.
--   Formalizes the use of `apd:eq:entry_bound` in `apd:eq:composition_majorant`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L224-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L224-L233

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.entryFactor_le_chainWeight_source {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    entryFactor kh1 c a m
      ≤ (1 + 4 * Real.exp 1 * betaOf kh1 c a)
        * (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by sorry
