-- Prove2me | Theorems.Thm_NashBargainingProblem_Axiomatic_sum_le_two_of_one_one_max
-- name    : NashBargainingProblem.Axiomatic.sum_le_two_of_one_one_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:39.203771+00:00
-- url     : https://prove2.me/theorems/b63ccd10-ebc3-4b90-97db-e34299a3767b
-- title:
--   p. 159 — if (1, 1) maximizes u₁u₂ on a convex S, no point of S has u₁ + u₂ > 2
-- statement:
--   Let $S\subseteq\mathbb R^2$ be convex, let $(1,1)\in S$, and suppose $(1,1)$ is a point of maximum of $u_1u_2$ over $S$ in the closed first quadrant: $s_1s_2\le1$ for every $s\in S$ with $s_1,s_2\ge0$. Then
--
--   $$
--   u_1+u_2\le 2\qquad\text{for every } u\in S .
--   $$
--
--   In Nash's proof this places the whole set of alternatives on one side of the line $u_1+u_2=2$, which touches the hyperbola $u_1u_2=1$ at $(1,1)$ (Figure 1).
--
--   **Formalization Note** The conclusion holds for every point of $S$, not only for those in the first quadrant, as the paper's "for no points of the set" says. The hypothesis is the weak maximum ($\le1$), which is what the paper's argument uses; the strict maximizer of the previous steps satisfies it.
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), p. 159, Two Person Theory, proof of the assertion ("For no points of the set will u1 + u2 > 2, now, since …"), Figure 1 (p. 160)

import Mathlib

namespace NashBargainingProblem.Axiomatic
theorem sum_le_two_of_one_one_max (S : Set (ℝ × ℝ))
    (hS_convex : Convex ℝ S) (h11 : ((1 : ℝ), (1 : ℝ)) ∈ S)
    (hmax : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s.1 * s.2 ≤ 1) :
    ∀ u ∈ S, u.1 + u.2 ≤ 2 := by sorry
end NashBargainingProblem.Axiomatic
