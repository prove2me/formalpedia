-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_proposition_4_1
-- name    : KleeWalkup67.FiveStep.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:17.492836+00:00
-- url     : https://prove2.me/theorems/b3a76518-d49e-4dfc-9d81-5aeb2df1a327
-- title:
--   4.1 PROPOSITION — property A of the middle face of a (1, d − 2, 1)-path gives δ_P(x, y) ≤ d
-- statement:
--   Let $d\ge2$ and let $(P,x,y)$ be a $d$-dimensional bounded simple Dantzig figure. Suppose $P$ admits a $(1,d-2,1)$-path $([x,x'],Q,[y',y])$ from $x$ to $y$: $[x,x']$ and $[y',y]$ are edges of $P$ ($1$-faces), $Q$ is a face of $P$ of dimension $d-2$, and $[x,x']\cap Q\ne\emptyset$, $Q\cap[y',y]\ne\emptyset$. If $Q$ has property A, then
--   $$\delta_P(x,y)\le d.$$
--
--   Together with 4.2 this proves the bounded 5-step conjecture: for $d=5$ the face $Q$ is a simple $3$-polytope with $6$, $7$ or $8$ facets.
--
--   **Formalization Note** Property A of $Q$ is taken relative to $Q$'s own dimension $m=d-2$ (facets of $Q$ are the $(d-3)$-faces of $P$ inside $Q$; classes of at most $d-1$ facets; a path in $Q$ of length at most $d-2$). The conclusion $\delta_P(x,y)\le d$ is `Hirsch.Reach P d x y`. The hypothesis $d\ge 2$ is implicit in the paper's $(1,d-2,1)$.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), p. 70, 4.1 PROPOSITION; property A defined on p. 69

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- 4.1 PROPOSITION, p. 70: if a `d`-dimensional bounded simple Dantzig figure `(P, x, y)` admits a
`(1, d − 2, 1)`-path `([x, x'], Q, [y', y])` such that `Q` has property A, then
`δ_P(x, y) ≤ d`. -/
theorem proposition_4_1 {d : ℕ} (hd : 2 ≤ d)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (hB : Bornology.IsBounded (Hirsch.Hpoly a b))
    (x' y' : EuclideanSpace ℝ (Fin d)) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hx' : IsFace a b (segment ℝ x x') ∧ dim (segment ℝ x x') = 1)
    (hQ : IsFace a b Q ∧ dim Q = d - 2)
    (hy' : IsFace a b (segment ℝ y' y) ∧ dim (segment ℝ y' y) = 1)
    (hxQ : (segment ℝ x x' ∩ Q).Nonempty) (hQy : (Q ∩ segment ℝ y' y).Nonempty)
    (hA : HasPropertyA a b Q) :
    Hirsch.Reach (Hirsch.Hpoly a b) d x y := by sorry

end KleeWalkup67.FiveStep
