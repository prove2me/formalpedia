-- Prove2me | Theorems.Thm_NashBargainingProblem_Axiomatic_nash_product_maximizer_exists_unique
-- name    : NashBargainingProblem.Axiomatic.nash_product_maximizer_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:27.139322+00:00
-- url     : https://prove2.me/theorems/aa336862-a443-48c4-8666-2933a643cde3
-- title:
--   p. 159 — on a compact convex S ∋ 0 with a point where both gain, u₁u₂ has exactly one maximizer in the first quadrant
-- statement:
--   Let $S\subseteq\mathbb R^2$ be a set of utility pairs $u=(u_1,u_2)$, where the anticipation of no cooperation has been given utility $0$ to both players. Assume that $S$ is compact and convex, that it contains the origin $(0,0)$, and that there is a possibility that both individuals could gain: some $s\in S$ has $s_1>0$ and $s_2>0$.
--
--   Then there is exactly one point $p\in S$ with $p_1>0$ and $p_2>0$ that maximizes the product $u_1u_2$ over the part of $S$ in the closed first quadrant, strictly:
--
--   $$
--   \forall s\in S,\quad s_1\ge 0,\ s_2\ge 0,\ s\ne p\ \Longrightarrow\ s_1s_2<p_1p_2 .
--   $$
--
--   This is the first step of Nash's proof: the point the axioms will single out exists (by compactness) and is unique (by convexity).
--
--   **Formalization Note** The paper's "first quadrant" is the closed quadrant $u_1\ge0,\ u_2\ge0$, and "the point where $u_1u_2$ is maximized" is read as the strict maximizer, in the form used by the goal theorem. The positivity $p_1,p_2>0$ is not written in the sentence; it follows from the point where both gain (p. 158) and is stated explicitly because the next step of the proof rescales $p$ to $(1,1)$.
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), p. 159, Two Person Theory, proof of the assertion ("We know some such point exists from the compactness. Convexity makes it unique."); standing assumptions p. 158 ("compact and convex", "a possibility that both individuals could gain")

import Mathlib

namespace NashBargainingProblem.Axiomatic
theorem nash_product_maximizer_exists_unique (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) (hS_zero : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (hS_gain : ∃ s ∈ S, 0 < s.1 ∧ 0 < s.2) :
    ∃! p : ℝ × ℝ, p ∈ S ∧ 0 < p.1 ∧ 0 < p.2 ∧
      ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2 := by sorry
end NashBargainingProblem.Axiomatic
