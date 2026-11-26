-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_crossing_pure_data
-- name    : FriedCrossing.Spectral.crossing_pure_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:22.75083+00:00
-- url     : https://prove2.me/theorems/0e176ff8-b28b-57f5-bd05-a6e5c7813c40
-- title:
--   Spectral: crossing pure data
-- statement:
--   THE EXACTNESS DICTIONARY. At a crossing (s_nc = 0 ≠ s_cl, locked branches in degree 2): if
--   the algebraic multiplicity of 0 in the degree-2 cluster is 2 (= 2·c₁ by exactness), then the pure
--   quadratic has 0 as a SIMPLE root: e₂ = 0 and e₁ ≠ 0 — the former `hexactZero` and `hgeneric`.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L674-L692
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L674-L692

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.crossing_pure_data {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    {scl snc : ℝ} (hne : scl ≠ snc) (hsnc : snc = 0) (hs : scl + snc = M.trace)
    (hp : scl * snc = M.det) (hlocked : ∀ z, M.charpoly.eval z = 0 → A.charpoly.eval z = 0)
    (hmult : A.charpoly.rootMultiplicity 0 = 2) : E₂ A M = 0 ∧ E₁ A M ≠ 0 := by sorry
