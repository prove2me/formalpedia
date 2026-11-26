-- Prove2me | Theorems.Thm_FriedCrossing_ClusterMatrix_charpoly_natDegree
-- name    : FriedCrossing.ClusterMatrix.charpoly_natDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:47:59.180325+00:00
-- url     : https://prove2.me/theorems/4d677931-5a85-4bc4-9486-75943a9ab6ab
-- title:
--   Cluster Matrix: charpoly nat Degree
-- statement:
--   The Cluster Matrix construction uses the charpoly nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L39-L40
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L39-L40

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix

theorem FriedCrossing.ClusterMatrix.charpoly_natDegree (A : Matrix (Fin 4) (Fin 4) ℝ) : A.charpoly.natDegree = 4 := by sorry
