-- Prove2me | Theorems.Thm_Lean4LPD_sum_reverse_choose
-- name    : Lean4LPD.sum_reverse_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:37.153286+00:00
-- url     : https://prove2.me/theorems/bd897184-9022-4c35-a0cb-335716531bda
-- title:
--   Lean4 LPD: sum reverse choose
-- statement:
--   The reversed hockey-stick count `∑_{j=1}^{m-1} C(m-j-1, k) = C(m-1, k+1)`, used to sum over
--   the final jump in `apd:eq:composition_majorant` and obtain the composition count in
--   `apd:eq:total_high_weight_norm`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L190-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L190-L194

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.sum_reverse_choose {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (∑ j ∈ Ico 1 m, ((m - j - 1).choose k : ℝ)) = ((m - 1).choose (k + 1) : ℝ) := by sorry
