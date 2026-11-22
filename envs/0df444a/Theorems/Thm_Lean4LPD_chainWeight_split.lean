-- Prove2me | Theorems.Thm_Lean4LPD_chainWeight_split
-- name    : Lean4LPD.chainWeight_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:42.456887+00:00
-- url     : https://prove2.me/theorems/b4e0c01b-aadc-479f-92a5-72d1b88c8f43
-- title:
--   Lean4 LPD: chain Weight split
-- statement:
--   Splitting off the final `j` single jumps, with no cancellation of the angle parameter.
--   Supporting algebra for `apd:eq:part_factor`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L69-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L69-L80

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.chainWeight_split (kh1 c a : ℝ) {j m : ℕ} (hjm : j ≤ m) :
    chainWeight kh1 c a m = a ^ j * chainWeight kh1 c a (m - j)
      * ∏ i ∈ range j, rungW kh1 c (m - j + i + 2) := by sorry
