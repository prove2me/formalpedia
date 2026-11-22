-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_sum_block_epsJump_le_cZero
-- name    : Lean4LPD.MultiLadder.sum_block_epsJump_le_cZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:10.105948+00:00
-- url     : https://prove2.me/theorems/059ca25b-8fc7-406b-923c-62c159ef8dc1
-- title:
--   Multi Ladder: sum block eps Jump le c Zero
-- statement:
--   **The quantitative `hstep` shape is a conclusion, not a hypothesis.**
--   This proves the scalar assembly in `apd:eq:total_high_weight_norm` / `apd:eq:c0` for reset
--   blocks obeying the concrete multi-jump layer recurrence. A Pauli model must still instantiate
--   `L`, `x`, their reset, and their local inflow, which `Lean4LPD/Pauli/LayerError.lean` does; no
--   equality with a post-cut retained mass is assumed. `A = αt` yields the exact input shape of
--   `total_truncation_error`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L376-L400
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L376-L400

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

theorem Lean4LPD.MultiLadder.sum_block_epsJump_le_cZero {kh1 c a A M : ℝ}
    (L : MultiLadder (epsJump kh1 c a) (entryFactor kh1 c a) M)
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : betaOf kh1 c a ≤ 1 / 2)
    (hA : 0 ≤ A) (hM : 0 ≤ M) {G r : ℕ} (hG : 1 ≤ G) (hr : 1 ≤ r)
    (haA : a ≤ A / (r : ℝ)) (m : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 (m + 1), epsJump kh1 c a j (m + 1) * L.N (m + 1 - j) (d * G + i)) +
        entryFactor kh1 c a (m + 1) * M) :
    (∑ d ∈ range r, x d G) ≤
      (cZero (r : ℝ) (m : ℝ) (G : ℝ) (4 * Real.exp 1 * betaOf kh1 c a) * G * A) ^ (m + 1) *
        (∏ j ∈ range (m + 1), rungW kh1 c (j + 2)) /
          (Nat.factorial (m + 1) : ℝ) * M := by sorry
