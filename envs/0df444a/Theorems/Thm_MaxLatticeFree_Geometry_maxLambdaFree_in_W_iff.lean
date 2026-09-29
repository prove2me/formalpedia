-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_maxLambdaFree_in_W_iff
-- name    : MaxLatticeFree.Geometry.maxLambdaFree_in_W_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:23:01.858994+00:00
-- url     : https://prove2.me/theorems/30501371-1d31-4527-ab62-c969477d7128
-- title:
--   Theorem 9 — maximal $\Lambda$-free convex sets of a subspace $W\supseteq V$
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$ and let $W$ be a linear space of $\mathbb R^n$ containing $V$, with $\dim W\ge1$. A set $S\subseteq\mathbb R^n$ is a maximal $\Lambda$-free convex set of $W$ if and only if one of the following holds:
--
--   1. $S$ is a polyhedron in $W$ with $\dim(S)=\dim(W)$, $S\cap V$ is a maximal $\Lambda$-free convex set of $V$, and the map
--   $$
--   F\longmapsto F\cap V
--   $$
--   is a bijection from the facets of $S$ onto the facets of $S\cap V$;
--   2. $S$ is an affine hyperplane of $W$ of the form $S=v+L$, where $v\in W$ and $L\subseteq W$ is a linear hyperplane of $W$, such that $L\cap V$ is a hyperplane of $V$ ($\dim(L\cap V)=\dim V-1$) that is not a $\Lambda$-subspace of $V$;
--   3. $S$ is a half-space of $W$, $S=\{x\in W\mid \langle a,x\rangle\le b\}$ with $a$ not orthogonal to $W$, that contains $V$ on its boundary: $\langle a,x\rangle=b$ for all $x\in V$.
--
--   Here $\Lambda$ may span a proper subspace $V$ of $W$, as happens for $\Lambda=\mathbb Z^n\cap W$ when $W$ is an irrational subspace (for example $W=\{x_1+x_2+\sqrt2x_3=0\}\subset\mathbb R^3$, whose integer points span $V=\{x_1+x_2=0,\ x_3=0\}$). The theorem reduces the classification in $W$ to Lovász's classification in $V$ (Theorem 10) and adds the two genuinely new cases (ii) and (iii). It is the geometric input for the characterization of minimal valid inequalities of the multi-row relaxation $R_f(W)$.
--
--   **Formalization Note** The page does not state $\dim W\ge1$; it is added because for $W=V=\{0\}$ the only maximal $\Lambda$-free set is $\emptyset$, which satisfies none of the three cases (the theorem as stated is true when $V=\{0\}\neq W$). "One-to-one correspondence, with $F\cap V$ the facet corresponding to $F$" is stated as: $F\cap V$ is a facet of $S\cap V$ for every facet $F$ of $S$, the map is injective, and every facet of $S\cap V$ is of this form. Dimensions are integer valued with $\dim\emptyset=-1$; hyperplane conditions are written $\dim L+1=\dim W$ in natural numbers.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 8, Theorem 9 (proof pp. 9–10)

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron

open Pointwise

namespace MaxLatticeFree.Geometry

theorem maxLambdaFree_in_W_iff {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hVW : V ≤ W)
    (hW : 0 < Module.finrank ℝ W) (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsMaxLambdaFree Λ W S ↔
      (IsPolyhedronIn W S ∧ affDim S = (Module.finrank ℝ W : ℤ) ∧
        IsMaxLambdaFree Λ V (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) ∧
        (∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) (F ∩ (V : Set (EuclideanSpace ℝ (Fin n))))) ∧
        (∀ F G : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet S G →
          F ∩ (V : Set (EuclideanSpace ℝ (Fin n))) = G ∩ (V : Set (EuclideanSpace ℝ (Fin n))) → F = G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsFacet (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) G →
          ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F ∧ F ∩ (V : Set (EuclideanSpace ℝ (Fin n))) = G)) ∨
      (∃ v ∈ W, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ W ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ W ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧
        Module.finrank ℝ (L ⊓ V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 = Module.finrank ℝ V ∧
        ¬ IsLambdaSubspace Λ V (L ⊓ V)) ∨
      (∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), (∃ w ∈ W, inner ℝ a w ≠ 0) ∧
        S = (W : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | inner ℝ a x ≤ b} ∧
        (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ {x | inner ℝ a x = b}) := by sorry

end MaxLatticeFree.Geometry
