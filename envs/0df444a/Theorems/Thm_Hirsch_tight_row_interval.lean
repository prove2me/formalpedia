-- Prove2me | Theorems.Thm_Hirsch_tight_row_interval
-- name    : Hirsch.tight_row_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:56.846071+00:00
-- url     : https://prove2.me/theorems/8ee09fc7-f854-4f4a-8754-84343044e16d
-- title:
--   Distances from a base vertex along a facet form an interval
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i<n\}$ be a bounded H-polytope, fix a base vertex $u$, and write $\mathrm{gdist}_P(u,\cdot)$ for the graph distance from $u$ (definition `Hirsch_walk`). Let $s$ be a row index and let $p,q$ be vertices of $P$ at which the $s$-th inequality is tight. Then for every integer $t$ with
--
--   $$\mathrm{gdist}_P(u,p)\ \le\ t\ \le\ \mathrm{gdist}_P(u,q)$$
--
--   there is a vertex $w$ of $P$ with $\langle a_s,w\rangle=b_s$ and $\mathrm{gdist}_P(u,w)=t$.
--
--   So the set of distances from $u$ realised on the face cut out by a given inequality is an interval of integers. This is the "connected layer family" property of polytope graphs isolated by Eisenbrand, Hähnle, Razborov and Rothvoß, in the form in which Larman's induction uses it: a facet active in two distance layers is active in every layer in between. It follows from connectivity of the graph of each face (`Hirsch.face_connected`: $p$ and $q$ are joined by a walk along which the $s$-th inequality stays tight) and the fact that the distance to $u$ changes by at most one along each step of a walk.
--
--   **Formalization Note** The vertices are the extreme points of $P$; boundedness guarantees that all graph distances are attained by walks (`Hirsch.gdist_reach`).
-- source:
--   F. Eisenbrand, N. Hähnle, A. Razborov, T. Rothvoß, Diameter of polyhedra: limits of abstraction, Math. Oper. Res. 35 (2010) 786-794, Section 2 (connected layer families, property that a facet meets consecutive layers); E. D. Kim, F. Santos, arXiv:0912.4235, proof of Theorem 2.5 ('each facet is active only in V_i's with consecutive values of i'). Platform ingredient: Hirsch.face_connected (ca7052f3-8364-4864-857f-55df4f138c51).

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk

open scoped RealInnerProductSpace

namespace Hirsch

theorem tight_row_interval (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (s : Fin n) (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ Set.extremePoints ℝ (Hpoly a b)) (hq : q ∈ Set.extremePoints ℝ (Hpoly a b))
    (hps : ⟪a s, p⟫ = b s) (hqs : ⟪a s, q⟫ = b s)
    (t : ℕ) (hpt : gdist (Hpoly a b) u p ≤ t) (htq : t ≤ gdist (Hpoly a b) u q) :
    ∃ w ∈ Set.extremePoints ℝ (Hpoly a b), ⟪a s, w⟫ = b s ∧ gdist (Hpoly a b) u w = t := by sorry

end Hirsch
