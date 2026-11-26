-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_charpoly_fin_two_factor
-- name    : FriedCrossing.Spectral.charpoly_fin_two_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:12.516388+00:00
-- url     : https://prove2.me/theorems/e5b4f57e-504e-4bc9-ba7b-df64d7bb06bc
-- title:
--   Spectral: charpoly fin two factor
-- statement:
--   The 2×2 characteristic polynomial factors through its two eigenvalues.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L623-L630
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L623-L630

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.charpoly_fin_two_factor {M : Matrix (Fin 2) (Fin 2) ℝ} {scl snc : ℝ}
    (hs : scl + snc = M.trace) (hp : scl * snc = M.det) :
    M.charpoly = (X - C scl) * (X - C snc) := by sorry
