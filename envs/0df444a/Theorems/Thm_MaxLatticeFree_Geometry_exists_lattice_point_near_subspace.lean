-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_exists_lattice_point_near_subspace
-- name    : MaxLatticeFree.Geometry.exists_lattice_point_near_subspace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:17:38.160971+00:00
-- url     : https://prove2.me/theorems/894b621a-a8d0-40fc-b140-7b8a4be27faf
-- title:
--   Lemma 18 — a non-lattice subspace has lattice points arbitrarily close to it
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$ and let $L$ be a linear subspace of $V$ that is not a $\Lambda$-subspace of $V$. Then for every $\varepsilon>0$ there exists
--
--   $$
--   y\in\Lambda\setminus L \quad\text{with}\quad \operatorname{dist}(y,L)<\varepsilon .
--   $$
--
--   This is the approximation property that makes an irrational hyperplane $v+L$ maximal lattice-free (Lemma 19): a slab around it, however thin, contains lattice points in its interior.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 12, Lemma 18

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace

namespace MaxLatticeFree.Geometry

theorem exists_lattice_point_near_subspace {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hLV : L ≤ V) (hL : ¬ IsLambdaSubspace Λ V L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ Λ, y ∉ L ∧ Metric.infDist y (L : Set (EuclideanSpace ℝ (Fin n))) < ε := by sorry

end MaxLatticeFree.Geometry
