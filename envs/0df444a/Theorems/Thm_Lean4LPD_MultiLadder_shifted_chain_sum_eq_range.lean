-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_shifted_chain_sum_eq_range
-- name    : Lean4LPD.MultiLadder.shifted_chain_sum_eq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:35.799025+00:00
-- url     : https://prove2.me/theorems/2cb5c899-3049-4943-9ab7-00dd2e11beaf
-- title:
--   Multi Ladder: shifted chain sum eq range
-- statement:
--   The merged chains in `apd:eq:total_high_weight_norm` have at most `m` jumps.
--   This cuts the shifted slot sum to `k < m` uniformly in the layer count `T`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L75-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L75-L87

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

theorem Lean4LPD.MultiLadder.shifted_chain_sum_eq_range {m : ℕ} (hm : 1 ≤ m) (T : ℕ) :
    (∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m) =
      ∑ k ∈ range m, (T.choose k : ℝ) * chain eps E (k + 1) m := by sorry
