-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_majorant_mono
-- name    : Lean4LPD.MultiLadder.majorant_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:28.380178+00:00
-- url     : https://prove2.me/theorems/8f6e5387-bf69-424c-aaac-af17e21b0c4a
-- title:
--   Multi Ladder: majorant mono
-- statement:
--   **The majorant is monotone in the number of layers.** This is what licenses bounding the
--   rung norms at the intermediate layers of a Trotter step by the majorant taken at the last layer of
--   the step. The rung norms themselves need not be monotone in the number of layers, so it is the
--   majorant, not the norm, that is moved to the end of the step; see `MultiLadder.block_inflow_le`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L325-L342
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L325-L342

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}
open Lean4LPD.MultiLadder
variable {M : ℝ}
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}

theorem Lean4LPD.MultiLadder.majorant_mono (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) (m T : ℕ) :
    majorant eps E M m T ≤ majorant eps E M m (T + 1) := by sorry
