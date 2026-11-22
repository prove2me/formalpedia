-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_majorant_inflow_eq_shifted_chain
-- name    : Lean4LPD.MultiLadder.majorant_inflow_eq_shifted_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:33.623292+00:00
-- url     : https://prove2.me/theorems/eb21f2d5-219f-43a0-b87a-1b89d526e727
-- title:
--   Multi Ladder: majorant inflow eq shifted chain
-- statement:
--   Merging the final inflow with `apd:eq:composition_majorant` gives a chain with one more
--   jump and no extra layer slot: the algebraic merge in `apd:eq:total_high_weight_norm`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L60-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L60-L71

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

theorem Lean4LPD.MultiLadder.majorant_inflow_eq_shifted_chain (m T : ℕ) :
    (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) T) + E m * M =
      M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m := by sorry
