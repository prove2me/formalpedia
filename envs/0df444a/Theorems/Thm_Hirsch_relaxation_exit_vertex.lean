-- Prove2me | Theorems.Thm_Hirsch_relaxation_exit_vertex
-- name    : Hirsch.relaxation_exit_vertex
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:45.174521+00:00
-- url     : https://prove2.me/theorems/9e275c18-78ca-4d9f-89bb-0147c532e83f
-- title:
--   An edge of a relaxation either is an edge of the polytope or exits it at a neighbouring vertex
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i<n\}$, let $T$ be a set of row indices, and let $Q\supseteq P$ be a set on which the inequalities indexed by $T$ hold. Let $x\in P$ and let $[x,y]$ be an edge of $Q$ (that is, $\mathrm{Adj}(Q,x,y)$: $x\ne y$ and the segment $[x,y]$ is an extreme subset of $Q$). Then:
--
--   1. if $y\in P$, the segment $[x,y]$ is an edge of $P$: $\mathrm{Adj}(P,x,y)$;
--   2. if $y\notin P$, there is a point $z\in[x,y]$ with $z=x$ or $\mathrm{Adj}(P,x,z)$, at which some inequality with index **outside** $T$ is tight:
--
--   $$\exists\, j\notin T,\quad \langle a_j,z\rangle=b_j .$$
--
--   In words: walking from $x$ along an edge of the relaxation, one either stays inside $P$ along an edge of $P$, or leaves $P$ through one of the dropped inequalities, and the exit point is $x$ itself or a neighbour of $x$ in $P$. This is the geometric content of the Kalai--Kleitman sentence "a shorter path in $Q$ could not be a path in $P$ and thus must meet a facet not in $F_v$"; no simplicity or general-position hypothesis is used.
--
--   **Formalization Note** The exit point $z$ is the last point of $[x,y]$ inside $P$; $P\cap[x,y]$ is an extreme subset of $P$ because $[x,y]$ is extreme in $Q\supseteq P$.
-- source:
--   G. Kalai, D. J. Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. AMS 26 (1992) 315-316, proof of the Lemma (the relaxed polyhedron cut out by the touched facets has no shorter paths), https://arxiv.org/abs/math/9204233; M. J. Todd, arXiv:1402.3579, Lemma 1. Prove2Me analogue for the full relaxation: Hirsch.relaxation_no_new_neighbours (ccfa0184-461a-49d1-b15d-1c6668e2d911).

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem relaxation_exit_vertex (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : Finset (Fin n)) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hPQ : Hpoly a b ⊆ Q) (hQ : ∀ z ∈ Q, ∀ j ∈ T, ⟪a j, z⟫ ≤ b j)
    (x y : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) (hadj : Adj Q x y) :
    (y ∈ Hpoly a b → Adj (Hpoly a b) x y) ∧
    (y ∉ Hpoly a b → ∃ z ∈ segment ℝ x y, (z = x ∨ Adj (Hpoly a b) x z) ∧
        ∃ j, j ∉ T ∧ ⟪a j, z⟫ = b j) := by sorry

end Hirsch
