-- Prove2me | Theorems.Thm_Hirsch_facet_reduction
-- name    : Hirsch.facet_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:36:49.735248+00:00
-- url     : https://prove2.me/theorems/9085c5d0-21fb-4760-abc7-a300b0562d59
-- title:
--   Facets are polyhedra of one dimension less
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_j,x\rangle\le b_j,\ j=1,\dots,n\}$ be a bounded H-polytope and fix an index $i$ with $a_i\ne 0$. The face $F_i=\{x\in P:\langle a_i,x\rangle=b_i\}$ is affinely isomorphic to an H-polyhedron in $\mathbb{R}^{d-1}$ cut out by the remaining $n-1$ inequalities, and the isomorphism carries vertices to vertices and edges to edges. Consequently, if every bounded H-polyhedron in $\mathbb{R}^{d-1}$ with $n-1$ inequalities has combinatorial diameter at most $B$, then any two vertices of $F_i$ are joined by a walk of $B$ steps in the vertex-edge graph of $P$ itself.
--
--   This is the recursion step of the Barnette--Larman and Kalai--Kleitman inductions: it makes precise, and usable inside a diameter induction, the sentence *each facet is affinely isomorphic to a $(d-1)$-polyhedron with at most $n-1$ facets*.
-- source:
--   M. J. Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, https://arxiv.org/abs/1402.3579, p. 1 (Introduction) and p. 2 (proof of Lemma 1); G. Kalai and D. J. Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. AMS 26 (1992) 315-316, p. 2

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem facet_reduction (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (hai : a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b)) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i})
    (hv : v ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end Hirsch
