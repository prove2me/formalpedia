-- Prove2me | Theorems.Thm_FriedCrossing_ClusterMatrix_eval_charpoly_eq_quartic
-- name    : FriedCrossing.ClusterMatrix.eval_charpoly_eq_quartic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:41:45.368189+00:00
-- url     : https://prove2.me/theorems/4ee91449-fe6e-4d68-886d-8a24659155d2
-- title:
--   Cluster Matrix: eval charpoly eq quartic
-- statement:
--   The characteristic polynomial of the degree-2 cluster matrix IS the quartic of the pure-zeros
--   file.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L44-L52
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L44-L52

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix

theorem FriedCrossing.ClusterMatrix.eval_charpoly_eq_quartic (A : Matrix (Fin 4) (Fin 4) ℝ) (z : ℝ) :
    A.charpoly.eval z = PureZeros.quartic (c₁ A) (c₂ A) (c₃ A) (c₄ A) z := by sorry
