-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_rootMultiplicity_zero_fin_two
-- name    : FriedCrossing.Spectral.rootMultiplicity_zero_fin_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:30.815511+00:00
-- url     : https://prove2.me/theorems/11ef4ad6-c348-4c2c-ac19-a19b0139d116
-- title:
--   Spectral: root Multiplicity zero fin two
-- statement:
--   At a crossing (snc = 0, scl ≠ 0): 0 is a SIMPLE eigenvalue of the degree-1 cluster.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L633-L640
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L633-L640

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.rootMultiplicity_zero_fin_two {M : Matrix (Fin 2) (Fin 2) ℝ} {scl snc : ℝ}
    (hne : scl ≠ snc) (hsnc : snc = 0) (hs : scl + snc = M.trace) (hp : scl * snc = M.det) :
    M.charpoly.rootMultiplicity 0 = 1 := by sorry
