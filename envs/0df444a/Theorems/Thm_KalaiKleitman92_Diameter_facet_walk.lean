-- Prove2me | Theorems.Thm_KalaiKleitman92_Diameter_facet_walk
-- name    : KalaiKleitman92.Diameter.facet_walk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:03:41.428493+00:00
-- url     : https://prove2.me/theorems/6c1c0cb0-f088-419f-8bab-dbcbfe0fb0f6
-- title:
--   p. 2, proof of Theorem 1 — the Δ(d − 1, n − 1) term: two vertices on a common facet are joined inside it, for unbounded polyhedra too
-- statement:
--   Let $P=\{x\in\mathbb R^d : \langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be a polyhedron cut out by $n=k+1$ linear inequalities, bounded or not, and let $i$ be a row with $a_i\ne0$. Consider the face
--
--   $$P_i=\{x\in P : \langle a_i,x\rangle=b_i\}$$
--
--   of $P$ on the hyperplane of row $i$. Suppose that every polyhedron in $\mathbb R^{d-1}$ cut out by $k=n-1$ inequalities, bounded or not, has graph diameter at most $B$. Then any two vertices $u,v$ of $P_i$ are joined by a walk of at most $B$ edges of $G(P)$ all of whose vertices lie in $P_i$.
--
--   In the proof of Theorem 1 this is the term $\Delta(d-1,n-1)$ in "the distance from $v$ to $u$ is at most $\Delta(d-1,n-1)+2\Delta(d,[n/2])+2$": the two balls around $v$ and $u$ reach a common facet, and the walk between the two contact vertices runs inside that facet, which is a polyhedron of dimension at most $d-1$ with at most $n-1$ facets.
--
--   **Formalization Note** The face is identified with a polyhedron in $\mathbb R^{d-1}$ cut out by the remaining $k$ rows; the hypothesis $a_i\ne0$ makes the hyperplane a genuine $(d-1)$-dimensional affine subspace (and forces $d\ge1$, so `Fin (d - 1)` is meaningful). A walk "of $B$ steps" allows stationary steps, so it has at most $B$ edges. The induction hypothesis ranges over all polyhedra in $\mathbb R^{d-1}$ with $k$ inequalities, with no boundedness: this is the unbounded version of the published bounded items `Hirsch.facet_reduction` and `Hirsch.facet_walk`.
-- source:
--   Kalai and Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. Amer. Math. Soc. 26 (1992), 315–316 (text of arXiv:math/9204233v1), p. 2, proof of Theorem 1 ("We obtained that the distance from v to u is at most ∆(d−1, n−1)+2∆(d, [n/2])+2")

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace KalaiKleitman92.Diameter

open Hirsch

/-- Kalai–Kleitman (1992), p. 2, proof of Theorem 1: the term Δ(d − 1, n − 1) in "the distance
from v to u is at most Δ(d−1, n−1) + 2Δ(d, [n/2]) + 2". Let `P = Hpoly a b ⊆ ℝ^d` be cut out by
`k + 1` inequalities, and let row `i` be nonzero. If every polyhedron in `ℝ^(d-1)` cut out by `k`
inequalities, bounded or not, has graph diameter at most `B`, then any two vertices `u`, `v` of
the face `{x ∈ P | ⟪a i, x⟫ = b i}` are joined by a walk of `B` steps along edges of `P` that
stays in that face. No boundedness is assumed. -/
theorem facet_walk (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (hai : a i ≠ 0) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i})
    (hv : v ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w B = v ∧
      (∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) ∧
      (∀ j ≤ B, w j ∈ Hpoly a b ∧ ⟪a i, w j⟫ = b i) := by sorry

end KalaiKleitman92.Diameter
