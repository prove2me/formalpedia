-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_sum_inflow_majorant_le
-- name    : Lean4LPD.MultiLadder.sum_inflow_majorant_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:40.199835+00:00
-- url     : https://prove2.me/theorems/48abe2fe-da04-4abd-9246-347edc6000cc
-- title:
--   Multi Ladder: sum inflow majorant le
-- statement:
--   The last-inflow majorants summed over steps satisfy the shifted slot count of
--   `apd:eq:total_high_weight_norm`: the outside `Γ` cancels the slot-bound denominator,
--   leaving exponent `K` and factorial `K!` for the chain with `K = k+1` jumps.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L92-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L92-L125

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

theorem Lean4LPD.MultiLadder.sum_inflow_majorant_le (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m)
    (hM : 0 ≤ M) {G m : ℕ} (hG : 1 ≤ G) (hm : 1 ≤ m) (r : ℕ) :
    (G : ℝ) * ∑ d ∈ range r,
      ((∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) ((d + 1) * G)) + E m * M) ≤
      M * ∑ k ∈ range m,
        ((((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
          chain eps E (k + 1) m := by sorry
