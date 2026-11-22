-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_sum_block_inflow_le_exp
-- name    : Lean4LPD.MultiLadder.sum_block_inflow_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:07.881836+00:00
-- url     : https://prove2.me/theorems/42196201-7cda-4cb4-8b49-1010333316fa
-- title:
--   Multi Ladder: sum block inflow le exp
-- statement:
--   The abstract reset/local-inflow route through the entire quantitative sector sum of
--   `apd:eq:total_high_weight_norm`. It still requires a concrete model to supply the
--   local inflow and local coefficient ratios; no final discarded-mass bound is assumed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L260-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L260-L277

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.MultiLadder.sum_block_inflow_le_exp {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ}
    {M C R : ℝ} (L : MultiLadder eps E M)
    (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M)
    (hC : 0 ≤ C) (hR : 0 ≤ R) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G) (hW : 0 ≤ W m)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (d * G + i)) + E m * M)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    (∑ d ∈ range r, x d G) ≤
      M * (C * W m * (((r : ℝ) + 1) * G) ^ m / (Nat.factorial m : ℝ) *
        Real.exp (R * (m : ℝ) ^ 2 / (((r : ℝ) + 1) * G))) := by sorry
