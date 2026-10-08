-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_lemma_4_2
-- name    : KleeWalkup67.FiveStep.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:24.780142+00:00
-- url     : https://prove2.me/theorems/715eacfa-8b35-4e7a-85de-7616b7e34535
-- title:
--   4.2 LEMMA — every simple 3-polytope with 6, 7, or 8 facets has property A
-- statement:
--   Let $P\subset\mathbb R^3$ be a simple $3$-polytope with $n$ facets, where $n\in\{6,7,8\}$. Then $P$ has property A: whenever its facets are divided into two disjoint classes $\mathfrak X,\mathfrak Y$ of at most $4$ facets each, and the sets $X$, $Y$ of vertices entirely surrounded by members of $\mathfrak X$, resp. $\mathfrak Y$, are both nonempty, some vertex of $X$ and some vertex of $Y$ are joined by a path of length at most $3$.
--
--   This is the case $d=5$ input for 4.1: the middle face of a $(1,3,1)$-path in a $5$-dimensional bounded simple Dantzig figure is a simple $3$-polytope with $6$ to $8$ facets. The paper's proof uses Euler's relation and Balinski's theorem that the graph of a $3$-polytope is $3$-connected.
--
--   **Formalization Note** $P$ is a bounded facet presentation with $n$ rows in $\mathbb R^3$; property A is applied to $Q=P$ itself (the face with no tight rows), of dimension $3$. The facet-count clause of property A ($6\le n\le 8$) holds by hypothesis.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), p. 70, 4.2 LEMMA; proof pp. 70–72

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- 4.2 LEMMA, p. 70: every simple 3-polytope with 6, 7, or 8 facets has property A. -/
theorem lemma_4_2 {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hF : IsFacetPresentation a b) (hB : Bornology.IsBounded (Hirsch.Hpoly a b))
    (hS : IsSimple a b) :
    HasPropertyA a b (Hirsch.Hpoly a b) := by sorry

end KleeWalkup67.FiveStep
