-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_bounded_maxLambdaFree_isPolytope
-- name    : MaxLatticeFree.Geometry.bounded_maxLambdaFree_isPolytope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:14:35.258738+00:00
-- url     : https://prove2.me/theorems/c0db5963-469f-4d8f-a00f-a33505efbb1c
-- title:
--   Lemma 13 — bounded full-dimensional maximal $\Lambda$-free sets are polytopes with lattice points on facets
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$. Let $S\subseteq V$ be a maximal $\Lambda$-free convex set of $V$ (interior taken relative to $V$) that is bounded and satisfies $\dim(S)=\dim(V)$. Then
--
--   $$
--   S \text{ is a polytope, and every facet } F \text{ of } S \text{ satisfies } \Lambda\cap\mathbf{relint}(F)\neq\emptyset .
--   $$
--
--   This is the bounded, full-dimensional case of the "only if" direction of Lovász's characterization (Theorem 10); the unbounded case is reduced to it by projecting out the lineality space.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 11, Lemma 13

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron

namespace MaxLatticeFree.Geometry

theorem bounded_maxLambdaFree_isPolytope {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ V S) (hbdd : Bornology.IsBounded S)
    (hdim : affDim S = (Module.finrank ℝ V : ℤ)) :
    IsPolytope S ∧ ∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → ∃ x ∈ Λ, x ∈ relint F := by sorry

end MaxLatticeFree.Geometry
