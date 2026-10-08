-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_proposition_3_4_b
-- name    : KleeWalkup67.FiveStep.proposition_3_4_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:46.101249+00:00
-- url     : https://prove2.me/theorems/97560fbb-4cef-4b58-8cee-f5b293a55531
-- title:
--   3.4 PROPOSITION (b) — a bounded simple Dantzig figure admits a (1, k₂, 1, k₄)-path
-- statement:
--   Let $(P,x,y)$ be a $d$-dimensional **bounded** simple Dantzig figure, and let $k_2,k_4$ be positive integers with
--   $$1+k_2+1+k_4=d.$$
--   Then $P$ admits a $(1,k_2,1,k_4)$-path from $x$ to $y$: an edge through $x$, a $k_2$-face, an edge, and a $k_4$-face containing $y$, consecutive members meeting.
--
--   With $k_2=d-3$, $k_4=1$ and the merging remark after 3.4, this yields the $(1,d-2,1)$-paths used in §4.
--
--   **Formalization Note** As for part (a), the proposition's joint hypothesis $k_1+1+k_3=d=1+k_2+1+k_4$ is split by part; part (b) involves only $k_2,k_4$.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), p. 66, 3.4 PROPOSITION (b)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- 3.4 PROPOSITION (b), p. 66: a `d`-dimensional bounded simple Dantzig figure admits a
`(1, k₂, 1, k₄)`-path from `x` to `y` whenever `k₂, k₄` are positive with
`1 + k₂ + 1 + k₄ = d`. -/
theorem proposition_3_4_b {d : ℕ}
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (hB : Bornology.IsBounded (Hirsch.Hpoly a b))
    (k₂ k₄ : ℕ) (hk₂ : 0 < k₂) (hk₄ : 0 < k₄) (hsum : 1 + k₂ + 1 + k₄ = d) :
    IsFacialPath a b [1, k₂, 1, k₄] x y := by sorry

end KleeWalkup67.FiveStep
