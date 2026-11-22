-- Prove2me | Theorems.Thm_Lean4LPD_exists_uniform_weight_cutoff
-- name    : Lean4LPD.exists_uniform_weight_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:51.535993+00:00
-- url     : https://prove2.me/theorems/2f371e37-b70c-4c75-bb0d-e005531222f0
-- title:
--   Lean4 LPD: exists uniform weight cutoff
-- statement:
--   A single weight cutoff works for the whole family when `k_o,k_h,q,c,M` are all fixed
--   uniform data. This is the norm-level, absolute-tolerance form of
--   `eq:truncation_weight_bound`, not a runtime or expectation theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L123-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L123-L130

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

theorem Lean4LPD.exists_uniform_weight_cutoff {ι : Type*} {error : ι → ℕ → ℝ} {q c M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ko kh : ℕ)
    (hbound : ∀ i m, 1 ≤ m → error i (ko + (kh - 1) * m) ≤
      q ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w m : ℕ, 1 ≤ m ∧ w = ko + (kh - 1) * m ∧ ∀ i, error i w ≤ ε := by sorry
