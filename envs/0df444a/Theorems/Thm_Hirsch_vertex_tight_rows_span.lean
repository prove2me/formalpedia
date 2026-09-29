-- Prove2me | Theorems.Thm_Hirsch_vertex_tight_rows_span
-- name    : Hirsch.vertex_tight_rows_span
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:41.420608+00:00
-- url     : https://prove2.me/theorems/12ef178c-2381-4524-a6d8-4a97df70ad72
-- title:
--   The normals of the inequalities tight at a vertex span the ambient space
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i<n\}$ and let $v$ be a vertex (extreme point) of $P$. If a vector $e\in\mathbb{R}^d$ is orthogonal to every normal $a_j$ whose inequality is tight at $v$,
--
--   $$\langle a_j,v\rangle=b_j\ \Longrightarrow\ \langle a_j,e\rangle=0 \qquad\text{for all } j,$$
--
--   then $e=0$. Equivalently, the normals of the tight inequalities at a vertex span $\mathbb{R}^d$.
--
--   This is the elementary half of the vertex/basic-feasible-solution dictionary: if some nonzero $e$ were orthogonal to all tight normals, the non-tight inequalities have positive slack at $v$, so $v\pm\varepsilon e\in P$ for small $\varepsilon>0$ and $v$ would be the midpoint of a segment in $P$. It is used to show that relaxations keeping the tight rows of a vertex still have trivial recession cone.
--
--   **Formalization Note** No boundedness or nonemptiness hypothesis is needed; $d=0$ and $n=0$ are allowed (for $d=0$ every $e$ is $0$).
-- source:
--   D. Bertsimas, J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Theorem 2.3 (p. 50), implication (a) => (c) with (c) as 'the active constraints span'; the direct perturbation argument in the proof there.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem vertex_tight_rows_span (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (e : EuclideanSpace ℝ (Fin d)) (he : ∀ j, ⟪a j, v⟫ = b j → ⟪a j, e⟫ = 0) :
    e = 0 := by sorry

end Hirsch
