-- Prove2me | Theorems.Thm_Lean4LPD_exists_model_norm_threshold
-- name    : Lean4LPD.exists_model_norm_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:57.812068+00:00
-- url     : https://prove2.me/theorems/8295492a-d5a3-464c-a1e6-e85c8cd4a7e8
-- title:
--   Lean4 LPD: exists model norm threshold
-- statement:
--   The model-only short-time condition `t < tZeroModel G kh α` supplies `0≤q<1` for
--   `q = decayBase G kh α t`, so the norm-level cutoff exists. This is the model-threshold
--   counterpart of `apd:thm:truncation_threshold_entangled`; it concerns the norm-level majorant
--   only, so no hypothesis on the input state is involved.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L136-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Threshold.lean#L136-L142

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

theorem Lean4LPD.exists_model_norm_threshold {G kh α t c M ε : ℝ}
    (hG : 0 < G) (hkh : 1 < kh) (hα : 0 < α) (ht : 0 ≤ t)
    (htime : t < tZeroModel G kh α) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ decayBase G kh α t ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε := by sorry
