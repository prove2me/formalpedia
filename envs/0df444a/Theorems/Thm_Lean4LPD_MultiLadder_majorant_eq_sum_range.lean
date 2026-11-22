-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_majorant_eq_sum_range
-- name    : Lean4LPD.MultiLadder.majorant_eq_sum_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:13.069805+00:00
-- url     : https://prove2.me/theorems/bdca684e-db2e-426f-b104-5f3fd893bfdb
-- title:
--   Multi Ladder: majorant eq sum range
-- statement:
--   The outer sum of `majorant` truncates at `m + 1` **uniformly in `T`**, which is what lets the
--   sum over Trotter steps be exchanged with it. Both directions vanish: terms with `k > m` have
--   `chain = 0` (a path to rung `m` cannot use more than `m` jumps), and terms with `k > T` have
--   `C(T,k) = 0` (there are not enough layers).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Assembly.lean#L50-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Assembly.lean#L50-L73

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Assembly
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}

theorem Lean4LPD.MultiLadder.majorant_eq_sum_range {m : ℕ} (hm : 1 ≤ m) (T : ℕ) :
    majorant eps E M m T = M * ∑ k ∈ range (m + 1), (T.choose k : ℝ) * chain eps E k m := by sorry
