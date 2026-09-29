-- Prove2me | Theorems.Thm_Hirsch_relaxation_vertex
-- name    : Hirsch.relaxation_vertex
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:23.210509+00:00
-- url     : https://prove2.me/theorems/f8866dfc-e7b2-4149-8414-380bf248046f
-- title:
--   A vertex of a polytope stays a vertex of any relaxation keeping its tight rows
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i<n\}$, let $T\subseteq\{0,\dots,n-1\}$ be a set of row indices, and let $Q\subseteq\mathbb{R}^d$ be any set on which the inequalities indexed by $T$ hold:
--
--   $$z\in Q,\ j\in T\ \Longrightarrow\ \langle a_j,z\rangle\le b_j .$$
--
--   Let $x$ be a vertex (extreme point) of $P$ with $x\in Q$, and suppose every inequality tight at $x$ has its index in $T$. Then $x$ is an extreme point of $Q$.
--
--   This is the "vertices survive the dropping of inequalities they do not touch" step of Kalai--Kleitman, stated for an arbitrary superset $Q$ (so that it applies to a relaxation intersected with a supporting hyperplane and with an auxiliary bounding cut). The reason is that the tight rows at $x$ contain $d$ linearly independent normals; on an open segment through $x$ inside $Q$ those rows are $\le b_j$ at the endpoints and $=b_j$ at $x$, hence tight at both endpoints, which forces the endpoints to coincide with $x$.
--
--   **Formalization Note** The hypothesis on $Q$ is only that the $T$-rows hold on $Q$; $Q$ need not be a polyhedron, and $P\subseteq Q$ is not assumed (only $x\in Q$).
-- source:
--   G. Kalai, D. J. Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. AMS 26 (1992) 315-316, proof of the Lemma (the relaxed polyhedron cut out by the touched facets has no shorter paths), https://arxiv.org/abs/math/9204233; M. J. Todd, arXiv:1402.3579, Lemma 1. Platform ingredient: LinearOptimization.lp_vertex_extreme_bfs_equiv (ea20915a-07e6-4e13-80cf-8dcecf2bb888), Bertsimas--Tsitsiklis Theorem 2.3.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem relaxation_vertex (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : Finset (Fin n)) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hQ : ∀ z ∈ Q, ∀ j ∈ T, ⟪a j, z⟫ ≤ b j)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Set.extremePoints ℝ (Hpoly a b)) (hxQ : x ∈ Q)
    (hxT : ∀ j, ⟪a j, x⟫ = b j → j ∈ T) :
    x ∈ Set.extremePoints ℝ Q := by sorry

end Hirsch
