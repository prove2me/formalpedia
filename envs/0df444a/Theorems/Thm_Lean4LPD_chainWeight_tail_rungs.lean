-- Prove2me | Theorems.Thm_Lean4LPD_chainWeight_tail_rungs
-- name    : Lean4LPD.chainWeight_tail_rungs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:38.547647+00:00
-- url     : https://prove2.me/theorems/027ae868-6c88-424d-8a44-16223ee07296
-- title:
--   Lean4 LPD: chain Weight tail rungs
-- statement:
--   The final `j` rung factors have exactly the denominator product in `partFactor j (m+c)`.
--   Supporting algebra for `apd:eq:part_factor`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L84-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L84-L95

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.chainWeight_tail_rungs (kh1 c : ℝ) {j m : ℕ} (hjm : j ≤ m) :
    (∏ i ∈ range j, rungW kh1 c (m - j + i + 2))
      = kh1 ^ j * ∏ i ∈ range j, ((m : ℝ) + c - j + 1 + i) := by sorry
