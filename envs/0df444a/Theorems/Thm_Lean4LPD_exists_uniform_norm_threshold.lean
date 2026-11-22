-- Prove2me | Theorems.Thm_Lean4LPD_exists_uniform_norm_threshold
-- name    : Lean4LPD.exists_uniform_norm_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:49.176267+00:00
-- url     : https://prove2.me/theorems/493d56f8-fda8-4e8e-bc72-bcbb2f823ecc
-- title:
--   Lean4 LPD: exists uniform norm threshold
-- statement:
--   The cutoff can be chosen independently of the family index **when the same `q,c,M`
--   majorizes the whole family**. This is the qualified dimension-independent interpretation of
--   `apd:thm:truncation_threshold_entangled`, for absolute norm tolerance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L110-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L110-L118

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

theorem Lean4LPD.exists_uniform_norm_threshold {ι : Type*} {error : ι → ℕ → ℝ} {q c M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ i m, 1 ≤ m → error i m ≤
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∀ i, error i m ≤ ε := by sorry
