-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_coeffs_of_mirror
-- name    : FriedCrossing.Spectral.coeffs_of_mirror
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:44:45.163729+00:00
-- url     : https://prove2.me/theorems/1c3079bf-c85d-4c72-9e96-4576129dc582
-- title:
--   Spectral: coeffs of mirror
-- statement:
--   spec A = {s, s, s, −s} ⇒ c₁ = 2s, c₂ = 0 (coefficient extraction at z = 0, ±1, 2).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L564-L572
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L564-L572

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.coeffs_of_mirror {A : Matrix (Fin 4) (Fin 4) ℝ} {s : ℝ}
    (h : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : c₁ A = 2 * s ∧ c₂ A = 0 := by sorry
