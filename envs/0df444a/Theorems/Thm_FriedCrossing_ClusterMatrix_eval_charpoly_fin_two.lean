-- Prove2me | Theorems.Thm_FriedCrossing_ClusterMatrix_eval_charpoly_fin_two
-- name    : FriedCrossing.ClusterMatrix.eval_charpoly_fin_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:42:53.32598+00:00
-- url     : https://prove2.me/theorems/a9d5a3ca-0ffa-4a56-9c54-19622a8cbed6
-- title:
--   Cluster Matrix: eval charpoly fin two
-- statement:
--   The 2×2 characteristic polynomial: z² − (tr M)z + det M.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L55-L59
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L55-L59

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix

theorem FriedCrossing.ClusterMatrix.eval_charpoly_fin_two (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ) :
    M.charpoly.eval z = z ^ 2 - M.trace * z + M.det := by sorry
