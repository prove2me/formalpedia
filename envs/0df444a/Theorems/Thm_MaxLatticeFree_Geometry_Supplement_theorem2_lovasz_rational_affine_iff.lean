-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_Supplement_theorem2_lovasz_rational_affine_iff
-- name    : MaxLatticeFree.Geometry.Supplement.theorem2_lovasz_rational_affine_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:01:38.129972+00:00
-- url     : https://prove2.me/theorems/1e2fc16b-8cc0-4eeb-a8d8-701fee006cc6
-- title:
--   Theorem 2 (corrected: dim V ≥ 1) — Lovász's characterization of maximal lattice-free convex sets of a rational affine space
-- statement:
--   Let $V\subseteq\mathbb R^n$ be a **rational** affine subspace, $V=\operatorname{aff}(V\cap\mathbb Z^n)$, of dimension at least $1$. Then a set $S$ is a maximal lattice-free convex set of $V$ if and only if one of the following holds:
--
--   1. $S$ is a polyhedron in $V$ of the form $S=P+L$, where $P$ is a polytope and $L$ is a rational linear space, with
--
--   $$
--   \dim S=\dim P+\dim L=\dim V ;
--   $$
--
--   no integral point lies in the relative interior of $S$, and every facet of $S$ has an integral point in its relative interior.
--   2. $S=v+L$ with $v\in V$ and $L$ an irrational hyperplane of the direction space of $V$.
--
--   The cylinders of case (i) are the classical maximal lattice-free sets used for intersection cuts; case (ii) is the possibility that only appears for irrational directions, and Theorem 1 reduces the irrational ambient case to this one.
--
--   **Formalization Note** $V$ is `affSpace z V₀` $=z+V_0$; rationality is `IsRationalAffine`. That $V$ contains an integral point, which the page also states, follows from rationality and $V\neq\emptyset$, so it is not a separate hypothesis. Relative interior is the interior relative to the affine hull; dimensions of sets are integer-valued with $\dim\emptyset=-1$. The containment $L\subseteq V_0$ in (i) is not written, as on the page; it follows from $S=P+L\subseteq V$ with $P\neq\emptyset$.
--
--   Differences from the source:
--   - correction: the characterization for every rational affine V with an integral point → the hypothesis dim V ≥ 1 (0 < finrank V₀); reason: for V = {z} with z integral the only maximal lattice-free set of V is ∅, which satisfies neither (i) (dim ∅ = −1 ≠ 0) nor (ii); the published Theorem 10 carries the same hypothesis, and no other V is excluded
--   - reading: L is an irrational hyperplane of V, with L linear and V affine → L ≤ V₀, dim L + 1 = dim V₀, L not a rational linear subspace; reason: a linear L can only be a hyperplane of the direction space of V; this is the reading of Theorem 10 on p. 8
--   - generalization: S ⊂ V → S an arbitrary subset of ℝⁿ; reason: each side of the equivalence already implies S ⊆ V, so restricting to S ⊆ V gives back the source statement
--   - encoding: S is a polyhedron in V → S is a polyhedron of ℝⁿ (published IsPolyhedronIn ⊤, i.e. finitely many closed half-spaces) with S ⊆ V; reason: V is itself the intersection of finitely many closed half-spaces of ℝⁿ, so a polyhedron in V is exactly a polyhedron of ℝⁿ contained in V; no instance changes
--   - encoding: V a rational affine subspace containing an integral point → V = z + V₀ with IsRationalAffine (z + V₀) and no separate integral-point hypothesis; reason: a nonempty affine space equal to the affine hull of its integral points contains one, so no instance changes
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, pp. 2–3, Theorem 2 (Lovász)

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_Rational

open Pointwise
open MaxLatticeFree.Inequalities

namespace MaxLatticeFree.Geometry.Supplement

theorem theorem2_lovasz_rational_affine_iff {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    (V₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrat : IsRationalAffine (affSpace z V₀))
    (hV : 0 < Module.finrank ℝ V₀)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsMaximalLatticeFree z V₀ S ↔
      (IsPolyhedronIn ⊤ S ∧ S ⊆ affSpace z V₀ ∧
        ∃ (P : Set (EuclideanSpace ℝ (Fin n))) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
          IsPolytope P ∧ IsRationalSubspace L ∧ S = P + (L : Set (EuclideanSpace ℝ (Fin n))) ∧
          affDim S = affDim P + (Module.finrank ℝ L : ℤ) ∧
          affDim P + (Module.finrank ℝ L : ℤ) = (Module.finrank ℝ V₀ : ℤ) ∧
          (∀ x ∈ relint S, x ∉ integralPoints n) ∧
          ∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F →
            ∃ x ∈ integralPoints n, x ∈ relint F) ∨
      (∃ v ∈ affSpace z V₀, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ V₀ ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ V₀ ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧ ¬ IsRationalSubspace L) := by sorry

end MaxLatticeFree.Geometry.Supplement
