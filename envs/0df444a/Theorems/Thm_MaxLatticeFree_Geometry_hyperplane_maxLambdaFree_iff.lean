-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_hyperplane_maxLambdaFree_iff
-- name    : MaxLatticeFree.Geometry.hyperplane_maxLambdaFree_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:18:16.482883+00:00
-- url     : https://prove2.me/theorems/2330f952-f036-451c-b965-bb60afabd172
-- title:
--   Lemma 19 — a hyperplane is maximal $\Lambda$-free iff it is not a lattice subspace
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$. Let $L$ be a linear subspace of $V$ with $\dim(L)=\dim(V)-1$ and let $v\in V$. Then
--
--   $$
--   v+L \text{ is a maximal } \Lambda\text{-free convex set of } V
--   \iff L \text{ is not a } \Lambda\text{-subspace of } V .
--   $$
--
--   This settles the lower-dimensional case of Lovász's characterization (Theorem 10(ii)): an affine hyperplane of $V$ is maximal exactly when its direction is irrational with respect to $\Lambda$.
--
--   **Formalization Note** $\dim(L)=\dim(V)-1$ is written $\dim L+1=\dim V$ in natural numbers, which excludes $V=\{0\}$.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 13, Lemma 19

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree

open Pointwise

namespace MaxLatticeFree.Geometry

theorem hyperplane_maxLambdaFree_iff {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hLV : L ≤ V)
    (hdim : Module.finrank ℝ L + 1 = Module.finrank ℝ V) (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ V) :
    IsMaxLambdaFree Λ V (v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n)))) ↔ ¬ IsLambdaSubspace Λ V L := by sorry

end MaxLatticeFree.Geometry
