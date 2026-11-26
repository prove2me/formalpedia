-- Prove2me | Theorems.Thm_FriedCrossing_Branch_zBranch_root
-- name    : FriedCrossing.Branch.zBranch_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:40.948998+00:00
-- url     : https://prove2.me/theorems/e5117440-31c5-5f47-95f7-3032d2ddb46e
-- title:
--   Branch: z Branch root
-- statement:
--   Wherever the discriminant is nonnegative, `zBranch` is a root of Q.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L739-L744
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L739-L744

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Branch
open TwinRate PureZeros

theorem FriedCrossing.Branch.zBranch_root (e₁ e₂ : ℝ → ℝ) (τ : ℝ) (hD : 0 ≤ disc (e₁ τ) (e₂ τ)) :
    zBranch e₁ e₂ τ ^ 2 - e₁ τ * zBranch e₁ e₂ τ + e₂ τ = 0 := by sorry
