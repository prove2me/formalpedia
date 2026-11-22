-- Prove2me | Theorems.Thm_Lean4LPD_exists_norm_threshold
-- name    : Lean4LPD.exists_norm_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:12.797011+00:00
-- url     : https://prove2.me/theorems/93cff17d-6d62-42eb-aab9-2efe66e97dd0
-- title:
--   Lean4 LPD: exists norm threshold
-- statement:
--   A natural cutoff rung satisfying the requested absolute norm tolerance, from
--   `apd:thm:truncation_threshold_entangled` at norm level only.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L101-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L101-L105

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Threshold
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Filter
open scoped Topology

theorem Lean4LPD.exists_norm_threshold {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (c M : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε := by sorry
