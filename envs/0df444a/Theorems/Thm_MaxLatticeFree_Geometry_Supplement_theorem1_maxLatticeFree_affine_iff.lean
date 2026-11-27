-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_Supplement_theorem1_maxLatticeFree_affine_iff
-- name    : MaxLatticeFree.Geometry.Supplement.theorem1_maxLatticeFree_affine_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:01:02.386135+00:00
-- url     : https://prove2.me/theorems/94d1dbc9-f7ac-49ce-9960-0ed47d6a2077
-- title:
--   Theorem 1 (corrected: dim W ≥ 1) — maximal lattice-free convex sets of an affine space with an integral point
-- statement:
--   Let $W\subseteq\mathbb R^n$ be an affine space of dimension at least $1$ containing an integral point $z_0$, and let $V=\operatorname{aff}(W\cap\mathbb Z^n)$ be the affine hull of its integral points; $V\subseteq W$, with equality exactly when $W$ is rational. A set $S$ is a **maximal lattice-free convex set of $W$** if $S\subseteq W$, $S$ is convex, no integral point lies in the interior of $S$ relative to $W$, and $S$ is inclusionwise maximal with these properties. Then $S$ is a maximal lattice-free convex set of $W$ if and only if one of the following holds:
--
--   1. $S$ is a polyhedron in $W$ with $\dim S=\dim W$; $S\cap V$ is a maximal lattice-free convex set of $V$ with $\dim(S\cap V)=\dim V$; and $F\mapsto F\cap V$ is a one-to-one correspondence from the facets of $S$ onto the facets of $S\cap V$.
--   2. $S=v+L$ is a hyperplane of $W$ ($v\in W$, $L$ a linear subspace of the direction of $W$ of codimension one in it) such that $L\cap\vec V$ is a hyperplane of the direction space $\vec V$ of $V$ and is irrational.
--   3. $S=W\cap\{x\mid \langle a,x\rangle\le b\}$ is a half-space of $W$ ($a$ not orthogonal to the direction of $W$) with $\langle a,x\rangle=b$ for every $x\in V$.
--
--   In symbols, for $S\subseteq\mathbb R^n$,
--
--   $$
--   S \text{ maximal lattice-free in } W\iff \text{(i)}\ \lor\ \text{(ii)}\ \lor\ \text{(iii)} .
--   $$
--
--   This is the integer-lattice, affine form of the paper's characterization; it describes exactly which convex sets give the nontrivial minimal cuts of Theorem 3 when the tableau data are irrational, and it reduces maximal lattice-free sets of an irrational $W$ to those of the rational space $V$ (Theorem 2).
--
--   **Formalization Note** $W$ is `affSpace z W₀` $=z+W_0$ and $V$ is `affHullInt z W₀`; "maximal lattice-free in $V$" is the published predicate with base point the integral point $z_0\in V$ and direction $\vec V$. Dimensions of sets are the integer-valued affine dimension with $\dim\emptyset=-1$; dimensions of $W,V,L$ are those of their direction spaces.
--
--   Differences from the source:
--   - correction: the characterization for every affine W with an integral point → the hypothesis dim W ≥ 1 (0 < finrank W₀); reason: for W = {z} with z integral the only maximal lattice-free set of W is ∅, which satisfies none of (i)–(iii); the published Theorem 9 carries the same hypothesis, and no other W is excluded
--   - reading: L ∩ V is an irrational hyperplane of V, with L linear and V affine → L ⊓ direction(V) has dimension dim V − 1 and is not a rational linear subspace; reason: the literal intersection L ∩ V can be empty when 0 ∉ V and is not generally the direction intersection; the restatement as Theorem 9 (p. 8) and the example on p. 3, where the irrationality of S ∩ V is that of its direction, read it in the direction space
--   - generalization: S ⊂ W → S an arbitrary subset of ℝⁿ; reason: each side of the equivalence already implies S ⊆ W, so restricting to S ⊆ W gives back the source statement
--   - encoding: W affine containing an integral point, V the affine hull of W ∩ ℤⁿ → W = z + W₀ with an integral z₀ ∈ W given, V = affHullInt z W₀, lattice-freeness in V taken with base point z₀ and direction of V; reason: every such W has this form and z₀ + direction(V) = V, so no instance changes
--   - encoding: S is a polyhedron in W → S is a polyhedron of ℝⁿ (published IsPolyhedronIn ⊤, i.e. finitely many closed half-spaces) with S ⊆ W; reason: W is itself the intersection of finitely many closed half-spaces of ℝⁿ, so a polyhedron in W is exactly a polyhedron of ℝⁿ contained in W; no instance changes
--   - encoding: S = v + L with v ∈ S; a half-space of W containing V on its boundary → v ∈ W; W ∩ {⟪a,x⟫ ≤ b} with a not orthogonal to W₀ and ⟪a,x⟫ = b on V; reason: v ∈ v + L holds automatically, and v ∈ W is what makes v + L a subset of W; the boundary of the half-space in W is W ∩ {⟪a,x⟫ = b} and V ⊆ W
--   - encoding: the facets of S and S ∩ V are in one-to-one correspondence with F ∩ V the facet corresponding to F → F ↦ F ∩ V maps facets of S to facets of S ∩ V, is injective on facets, and every facet of S ∩ V is of this form; reason: the same bijection, spelled out as in the published Theorem 9
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 2, Theorem 1

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_Rational

open Pointwise
open MaxLatticeFree.Inequalities

namespace MaxLatticeFree.Geometry.Supplement

theorem theorem1_maxLatticeFree_affine_iff {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    (W₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (z₀ : EuclideanSpace ℝ (Fin n))
    (hz₀ : z₀ ∈ affSpace z W₀ ∩ integralPoints n) (hW : 0 < Module.finrank ℝ W₀)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsMaximalLatticeFree z W₀ S ↔
      (IsPolyhedronIn ⊤ S ∧ S ⊆ affSpace z W₀ ∧ affDim S = (Module.finrank ℝ W₀ : ℤ) ∧
        IsMaximalLatticeFree z₀ (affHullInt z W₀).direction
          (S ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n)))) ∧
        affDim (S ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n)))) =
          (Module.finrank ℝ (affHullInt z W₀).direction : ℤ) ∧
        (∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F →
          IsFacet (S ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))))
            (F ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))))) ∧
        (∀ F G : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet S G →
          F ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))) =
            G ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))) → F = G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)),
          IsFacet (S ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n)))) G →
          ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F ∧
            F ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))) = G)) ∨
      (∃ v ∈ affSpace z W₀, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ W₀ ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ W₀ ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧
        Module.finrank ℝ (L ⊓ (affHullInt z W₀).direction :
          Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 =
            Module.finrank ℝ (affHullInt z W₀).direction ∧
        ¬ IsRationalSubspace (L ⊓ (affHullInt z W₀).direction)) ∨
      (∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), (∃ w ∈ W₀, inner ℝ a w ≠ 0) ∧
        S = affSpace z W₀ ∩ {x | inner ℝ a x ≤ b} ∧
        (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))) ⊆ {x | inner ℝ a x = b}) := by sorry

end MaxLatticeFree.Geometry.Supplement
