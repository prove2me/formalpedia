-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_sum_block_inflow_le
-- name    : Lean4LPD.MultiLadder.sum_block_inflow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:53.018087+00:00
-- url     : https://prove2.me/theorems/64a339a4-997f-407c-bf13-8ddf3f457752
-- title:
--   Multi Ladder: sum block inflow le
-- statement:
--   The reset-and-layer-inflow route to the merged-chain bound of
--   `apd:eq:total_high_weight_norm`. `x d i` is the within-step mass before the final cut; its reset
--   and per-layer recurrence are explicit premises, not an assumed end-to-end truncation bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L166-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L166-L180

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}

theorem Lean4LPD.MultiLadder.sum_block_inflow_le (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m)
    (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (d * G + i)) + E m * M) :
    (∑ d ∈ range r, x d G) ≤ M * ∑ k ∈ range m,
      ((((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
        chain eps E (k + 1) m := by sorry
