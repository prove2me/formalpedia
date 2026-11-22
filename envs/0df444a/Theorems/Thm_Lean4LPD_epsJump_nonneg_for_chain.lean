-- Prove2me | Theorems.Thm_Lean4LPD_epsJump_nonneg_for_chain
-- name    : Lean4LPD.epsJump_nonneg_for_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:26.877597+00:00
-- url     : https://prove2.me/theorems/92262031-eec3-4d2e-ba46-997ef7dfa4a2
-- title:
--   Lean4 LPD: eps Jump nonneg for chain
-- statement:
--   `epsJump` is nonnegative at every index required by the generic chain theorem, including
--   the otherwise-unneeded `(j,m)=(0,0)` case, where its value is one.
--   Supporting sign check for `apd:eq:composition_majorant`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L199-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L199-L208

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.epsJump_nonneg_for_chain {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (j m : ℕ) :
    0 ≤ epsJump kh1 c a j m := by sorry
