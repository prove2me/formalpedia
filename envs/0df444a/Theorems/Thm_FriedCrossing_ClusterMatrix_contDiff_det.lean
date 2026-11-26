-- Prove2me | Theorems.Thm_FriedCrossing_ClusterMatrix_contDiff_det
-- name    : FriedCrossing.ClusterMatrix.contDiff_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:49:19.138427+00:00
-- url     : https://prove2.me/theorems/800a4631-87d0-4a28-927d-5e4601e9e97b
-- title:
--   Cluster Matrix: cont Diff det
-- statement:
--   The determinant is a polynomial in the entries.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L83-L86
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L83-L86

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem FriedCrossing.ClusterMatrix.contDiff_det {n : Type*} [Fintype n] [DecidableEq n] {A : E → Matrix n n ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) : ContDiff ℝ k fun x => (A x).det := by sorry
