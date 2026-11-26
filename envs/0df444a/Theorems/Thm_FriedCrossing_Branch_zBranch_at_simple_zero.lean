-- Prove2me | Theorems.Thm_FriedCrossing_Branch_zBranch_at_simple_zero
-- name    : FriedCrossing.Branch.zBranch_at_simple_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:44.749795+00:00
-- url     : https://prove2.me/theorems/f3e2fdca-72a5-4b42-8869-87f364c4e104
-- title:
--   Branch: z Branch at simple zero
-- statement:
--   At a point where Q has the SIMPLE root 0 (e₂ = 0, e₁ ≠ 0) and e₁, e₂ are continuous, the
--   nearest-zero branch vanishes and is continuous — the former `hbranch`.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L748-L789
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L748-L789

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Branch
open TwinRate PureZeros

theorem FriedCrossing.Branch.zBranch_at_simple_zero {e₁ e₂ : ℝ → ℝ} {σ : ℝ} (hc₁ : ContinuousAt e₁ σ)
    (hc₂ : ContinuousAt e₂ σ) (h₂ : e₂ σ = 0) (h₁ : e₁ σ ≠ 0) :
    ContinuousAt (zBranch e₁ e₂) σ ∧ zBranch e₁ e₂ σ = 0 := by sorry
