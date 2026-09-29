-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_lattice_map_orthogonalProjection
-- name    : MaxLatticeFree.Geometry.lattice_map_orthogonalProjection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:16:49.266038+00:00
-- url     : https://prove2.me/theorems/2e424ab7-bb83-405a-9ad3-77ba62be1874
-- title:
--   Lemma 17 — projecting a lattice along a lattice subspace gives a lattice
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$ and let $L$ be a $\Lambda$-subspace of $V$. Let $\pi$ be the orthogonal projection of $\mathbb R^n$ onto the orthogonal complement $L^\perp$. Then
--
--   $$
--   \pi(\Lambda)=\{\pi(y)\mid y\in\Lambda\}\ \text{ is a lattice of the linear space } L^\perp\cap V .
--   $$
--
--   The hypothesis that $L$ has a basis in $\Lambda$ is essential: projecting $\mathbb Z^2$ along an irrational line gives a dense subgroup of the orthogonal line. The lemma lets the proof of Theorem 10 pass from an unbounded set $P+L$ to the bounded set $P$ in the lower-dimensional space $L^\perp\cap V$.
--
--   **Formalization Note** The paper writes $\operatorname{proj}_{L^\perp}(S)=\{v\in L^\perp\mid v+w\in S \text{ for some } w\in L\}$; this is the image of $S$ under the orthogonal projection onto $L^\perp$, formalized as the image of $\Lambda$ under `Lᗮ.starProjection`.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 12, Lemma 17 (citing Barvinok, A Course in Convexity, p. 284, problem 3)

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace

namespace MaxLatticeFree.Geometry

theorem lattice_map_orthogonalProjection {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hL : IsLambdaSubspace Λ V L) :
    IsLatticeOf (Λ.map (Lᗮ.starProjection : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap.toAddMonoidHom)
      (Lᗮ ⊓ V) := by sorry

end MaxLatticeFree.Geometry
