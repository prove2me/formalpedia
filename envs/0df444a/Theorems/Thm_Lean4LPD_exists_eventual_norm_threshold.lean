-- Prove2me | Theorems.Thm_Lean4LPD_exists_eventual_norm_threshold
-- name    : Lean4LPD.exists_eventual_norm_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:14.692227+00:00
-- url     : https://prove2.me/theorems/a76fc515-2db4-4f26-8c28-932bc1e318f9
-- title:
--   Lean4 LPD: exists eventual norm threshold
-- statement:
--   Every sufficiently large natural rung meets the norm tolerance, the existence part of
--   `apd:thm:truncation_threshold_entangled`. No explicit logarithmic formula for the rung is
--   asserted, and no hypothesis on the input state is involved.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L88-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L88-L97

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

theorem Lean4LPD.exists_eventual_norm_threshold {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m →
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε := by sorry
