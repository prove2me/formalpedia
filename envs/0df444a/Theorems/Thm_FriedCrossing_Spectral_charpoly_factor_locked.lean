-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_charpoly_factor_locked
-- name    : FriedCrossing.Spectral.charpoly_factor_locked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:23.578236+00:00
-- url     : https://prove2.me/theorems/41f0dbbc-54a1-4f7f-ab08-2d2a65934900
-- title:
--   Spectral: charpoly factor locked
-- statement:
--   LOCKED BRANCHES: if the two degree-1 eigenvalues (distinct) are degree-2 eigenvalues, the
--   degree-2 characteristic polynomial factors as (X − s_cl)(X − s_nc)·Q with Q the pure quadratic of
--   E₁, E₂ (quartic division).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L645-L659
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L645-L659

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.charpoly_factor_locked {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    {scl snc : ℝ} (hne : scl ≠ snc) (hs : scl + snc = M.trace) (hp : scl * snc = M.det)
    (hlocked : ∀ z, M.charpoly.eval z = 0 → A.charpoly.eval z = 0) :
    A.charpoly = (X - C scl) * (X - C snc) * Qpoly (E₁ A M) (E₂ A M) := by sorry
