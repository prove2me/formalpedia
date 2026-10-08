-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_proposition_3_4_a
-- name    : KleeWalkup67.FiveStep.proposition_3_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:04:05.80992+00:00
-- url     : https://prove2.me/theorems/5aefaa63-4c5e-429e-b26b-8fc70d3ce7c4
-- title:
--   3.4 PROPOSITION (a) — a simple Dantzig figure admits a (k₁, 1, k₃)-path
-- statement:
--   Let $(P,x,y)$ be a $d$-dimensional simple Dantzig figure: $P\subset\mathbb R^d$ is a simple $d$-polyhedron (bounded or not) with $2d$ facets, $x,y$ are vertices, $d$ facets are incident to $x$ and the $d$ others to $y$. Let $k_1,k_3$ be positive integers with
--   $$k_1+1+k_3=d.$$
--   Then $P$ admits a $(k_1,1,k_3)$-path from $x$ to $y$: a face $K_1\ni x$ of dimension $k_1$, an edge $K_2$, and a face $K_3\ni y$ of dimension $k_3$, with $K_1\cap K_2\ne\emptyset$ and $K_2\cap K_3\ne\emptyset$.
--
--   This is the first of the paper's facial-path results; part (b) for bounded figures is obtained from it through 3.1.
--
--   **Formalization Note** The proposition on p. 66 introduces $k_1,\dots,k_4$ together with $k_1+1+k_3=d=1+k_2+1+k_4$; part (a) involves only $k_1,k_3$, and is stated with those alone, as the opening of §3 (p. 64) does: "any simple Dantzig figure admits a $(k_1,1,k_3)$-path". This also covers $d=3$, where no positive $k_2,k_4$ exist.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), p. 66, 3.4 PROPOSITION (a); p. 64, opening of §3

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- 3.4 PROPOSITION (a), p. 66: a `d`-dimensional simple Dantzig figure admits a
`(k₁, 1, k₃)`-path from `x` to `y` whenever `k₁, k₃` are positive with `k₁ + 1 + k₃ = d`. -/
theorem proposition_3_4_a {d : ℕ}
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (k₁ k₃ : ℕ) (hk₁ : 0 < k₁) (hk₃ : 0 < k₃) (hsum : k₁ + 1 + k₃ = d) :
    IsFacialPath a b [k₁, 1, k₃] x y := by sorry

end KleeWalkup67.FiveStep
