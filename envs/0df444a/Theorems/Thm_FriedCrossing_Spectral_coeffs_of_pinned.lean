-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_coeffs_of_pinned
-- name    : FriedCrossing.Spectral.coeffs_of_pinned
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:43:34.319616+00:00
-- url     : https://prove2.me/theorems/25025069-6ced-4c8e-8451-af16010ebe26
-- title:
--   Spectral: coeffs of pinned
-- statement:
--   spec A = {0, 0, 0, t} ⇒ c₁ = t, c₂ = 0.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L575-L583
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L575-L583

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.coeffs_of_pinned {A : Matrix (Fin 4) (Fin 4) ℝ} {t : ℝ}
    (h : ∀ z, A.charpoly.eval z = z ^ 3 * (z - t)) : c₁ A = t ∧ c₂ A = 0 := by sorry
