-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_block_inflow_le
-- name    : Lean4LPD.MultiLadder.block_inflow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:36.790803+00:00
-- url     : https://prove2.me/theorems/032df072-f56e-44f3-a30f-3154fa2e3b6b
-- title:
--   Multi Ladder: block inflow le
-- statement:
--   Iterate the per-layer inflow from a reset state over the `G` layers of a block, as in the
--   first step of `apd:eq:total_high_weight_norm`. Only the majorant, not the lower-rung norms
--   themselves, is moved to the end of the block (`majorant_mono`). The local recurrence `hinflow`
--   and the reset `hreset` must be supplied by the model.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L131-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L131-L161

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

theorem Lean4LPD.MultiLadder.block_inflow_le (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m)
    (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) {m T G : ℕ}
    (x : ℕ → ℝ) (hreset : x 0 = 0)
    (hinflow : ∀ i, i < G → x (i + 1) ≤ x i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (T + i)) + E m * M) :
    x G ≤ (G : ℝ) *
      ((∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G)) + E m * M) := by sorry
