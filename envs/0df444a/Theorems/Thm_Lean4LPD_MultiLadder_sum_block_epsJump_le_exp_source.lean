-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_sum_block_epsJump_le_exp_source
-- name    : Lean4LPD.MultiLadder.sum_block_epsJump_le_exp_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:16.145868+00:00
-- url     : https://prove2.me/theorems/80bd8bf9-a407-44c1-885b-a194d02159f9
-- title:
--   Multi Ladder: sum block eps Jump le exp source
-- statement:
--   The concrete `epsJump`/`entryFactor` specialization of `apd:eq:total_high_weight_norm`,
--   with the paper's entry constant `1 + 4eβ`. All local coefficient and entry premises are
--   discharged by `ChainWeights`; only the model's reset and layer-inflow recurrence remain inputs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L346-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L346-L368

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

theorem Lean4LPD.MultiLadder.sum_block_epsJump_le_exp_source {kh1 c a M : ℝ}
    (L : MultiLadder (epsJump kh1 c a) (entryFactor kh1 c a) M)
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : betaOf kh1 c a ≤ 1 / 2)
    (hM : 0 ≤ M) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, epsJump kh1 c a j m * L.N (m - j) (d * G + i)) +
        entryFactor kh1 c a m * M) :
    (∑ d ∈ range r, x d G) ≤
      M * ((1 + 4 * Real.exp 1 * betaOf kh1 c a) * chainWeight kh1 c a m *
        (((r : ℝ) + 1) * G) ^ m / (Nat.factorial m : ℝ) *
          Real.exp (9 / 4 * (m : ℝ) ^ 2 / (((r : ℝ) + 1) * G))) := by sorry
