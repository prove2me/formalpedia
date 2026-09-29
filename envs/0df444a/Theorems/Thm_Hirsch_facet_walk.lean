-- Prove2me | Theorems.Thm_Hirsch_facet_walk
-- name    : Hirsch.facet_walk
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:24.160986+00:00
-- url     : https://prove2.me/theorems/bfe32cd8-4b1b-4e12-a824-22f7182b302b
-- title:
--   Facets are polyhedra of one dimension less, with the connecting walk staying in the facet
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_j,x\rangle\le b_j,\ j\le k\}$ be a bounded H-polytope described by $k+1$ inequalities and fix an index $i$ with $a_i\ne0$. Let $F_i=\{x\in P:\langle a_i,x\rangle=b_i\}$. Suppose that every bounded H-polyhedron in $\mathbb{R}^{d-1}$ described by $k$ inequalities has combinatorial diameter at most $B$. Then any two vertices $u,v$ of $F_i$ are joined by a walk $w_0=u,\dots,w_B=v$ of $B$ steps in the vertex-edge graph of $P$ **all of whose points lie in $F_i$**:
--
--   $$w_j\in P\quad\text{and}\quad\langle a_i,w_j\rangle=b_i\qquad(0\le j\le B).$$
--
--   This strengthens the platform theorem `Hirsch.facet_reduction` (same hypotheses) by recording that the walk produced by the affine chart of the facet never leaves the supporting hyperplane. The extra information is what a layer argument needs: it identifies walks in the facet, viewed as a $(d-1)$-polyhedron with $k$ inequalities, with walks in $P$ that stay on that facet.
--
--   **Formalization Note** The facet is written as the set $\{x\mid x\in \mathrm{Hpoly}\ a\ b\wedge\langle a_i,x\rangle=b_i\}$ and its vertices as its extreme points, exactly as in `Hirsch.facet_reduction`; the walk is indexed by $\mathbb{N}$ with stationary steps allowed.
-- source:
--   M. J. Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579, p. 1-2 (each facet is a (d-1)-polyhedron with at most n-1 facets); strengthening of Prove2Me Hirsch.facet_reduction (11b3500a-b9f8-4b44-94aa-d71354441ddb), whose accepted proof d0ea5375-6c35-4963-a148-56a6a49b70b9 already constructs the walk inside the facet.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem facet_walk (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (hai : a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b)) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i})
    (hv : v ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w B = v ∧
      (∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) ∧
      (∀ j ≤ B, w j ∈ Hpoly a b ∧ ⟪a i, w j⟫ = b i) := by sorry

end Hirsch
