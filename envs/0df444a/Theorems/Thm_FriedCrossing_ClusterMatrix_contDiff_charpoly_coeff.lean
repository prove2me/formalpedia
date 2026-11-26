-- Prove2me | Theorems.Thm_FriedCrossing_ClusterMatrix_contDiff_charpoly_coeff
-- name    : FriedCrossing.ClusterMatrix.contDiff_charpoly_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:42:33.736682+00:00
-- url     : https://prove2.me/theorems/47d82525-35de-559b-aba0-ce82a4aaaa74
-- title:
--   Cluster Matrix: cont Diff charpoly coeff
-- statement:
--   Characteristic coefficients are signed sums of principal minors (Mathlib), hence polynomial
--   in the entries.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L90-L100
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L90-L100

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem FriedCrossing.ClusterMatrix.contDiff_charpoly_coeff {A : E → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) (m : ℕ) (hm : m ≤ 4) :
    ContDiff ℝ k fun x => (A x).charpoly.coeff (4 - m) := by sorry
