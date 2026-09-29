-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_lovasz_maxLambdaFree_iff
-- name    : MaxLatticeFree.Geometry.lovasz_maxLambdaFree_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:20:47.182981+00:00
-- url     : https://prove2.me/theorems/65012352-ecc1-42d3-b66a-9122e22ad0c1
-- title:
--   Theorem 10 — Lovász's characterization of maximal $\Lambda$-free convex sets of $V$
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$ with $\dim V\ge1$. A set $S\subseteq\mathbb R^n$ is a maximal $\Lambda$-free convex set of $V$ if and only if one of the following holds:
--
--   1. $S$ is a polyhedron in $V$ of the form $S=P+L$ where $P$ is a polytope, $L$ is a $\Lambda$-subspace of $V$,
--   $$
--   \dim(S)=\dim(P)+\dim(L)=\dim(V),
--   $$
--   no point of $\Lambda$ lies in $\mathbf{int}_V(S)$, and every facet of $S$ has a point of $\Lambda$ in its relative interior;
--   2. $S$ is an affine hyperplane of $V$ of the form $S=v+L$, where $v\in V$, $L$ is a linear subspace of $V$ with $\dim L=\dim V-1$, and $L$ is not a $\Lambda$-subspace of $V$.
--
--   For $\Lambda=\mathbb Z^n\cap V$ this is Lovász's theorem (Theorem 2 of the paper): maximal lattice-free convex sets are cylinders over polytopes with a lattice point in the relative interior of every facet, or irrational hyperplanes.
--
--   **Formalization Note** The page does not state $\dim V\ge1$; it is added because for $V=\{0\}$ the only maximal $\Lambda$-free set is $\emptyset$ ($\mathbf{int}_{\{0\}}\{0\}=\{0\}\ni 0$), which satisfies neither case. "$S$ is a polyhedron" is read as a polyhedron in $V$, because a maximal $\Lambda$-free set of $V$ lies in $V$. "Its interior" is $\mathbf{int}_V$, as fixed on p. 10. $S=P+L$ is the Minkowski sum.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 8, Theorem 10 (proof pp. 13–15)

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron

open Pointwise

namespace MaxLatticeFree.Geometry

theorem lovasz_maxLambdaFree_iff {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hV : 0 < Module.finrank ℝ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsMaxLambdaFree Λ V S ↔
      (IsPolyhedronIn V S ∧
        ∃ (P : Set (EuclideanSpace ℝ (Fin n))) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
          IsPolytope P ∧ IsLambdaSubspace Λ V L ∧ S = P + (L : Set (EuclideanSpace ℝ (Fin n))) ∧
          affDim S = affDim P + (Module.finrank ℝ L : ℤ) ∧
          affDim P + (Module.finrank ℝ L : ℤ) = (Module.finrank ℝ V : ℤ) ∧
          (Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ intW (V : Set (EuclideanSpace ℝ (Fin n))) S = ∅ ∧
          ∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → ∃ x ∈ Λ, x ∈ relint F) ∨
      (∃ v ∈ V, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ V ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ V ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧ ¬ IsLambdaSubspace Λ V L) := by sorry

end MaxLatticeFree.Geometry
