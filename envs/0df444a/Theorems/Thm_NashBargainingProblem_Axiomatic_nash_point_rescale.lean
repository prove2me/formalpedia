-- Prove2me | Theorems.Thm_NashBargainingProblem_Axiomatic_nash_point_rescale
-- name    : NashBargainingProblem.Axiomatic.nash_point_rescale
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:33.126975+00:00
-- url     : https://prove2.me/theorems/77113454-b8f1-4d4e-a217-dc5e8c92a4ba
-- title:
--   p. 159 — multiplying the utilities by positive constants moves the maximizer of u₁u₂ accordingly
-- statement:
--   Let $S\subseteq\mathbb R^2$ and let $p\in S$ with $p_1\ge0$, $p_2\ge0$ be the strict maximizer of $u_1u_2$ over $S$ in the closed first quadrant: every $s\in S$ with $s_1,s_2\ge0$ and $s\ne p$ has $s_1s_2<p_1p_2$. Let $\alpha_1,\alpha_2>0$, and let
--
--   $$
--   S'=\{(\alpha_1u_1,\ \alpha_2u_2) : u\in S\},\qquad p'=(\alpha_1p_1,\ \alpha_2p_2)
--   $$
--
--   be the images under the change of utility scales $u\mapsto(\alpha_1u_1,\alpha_2u_2)$. Then $p'\in S'$, $p'_1,p'_2\ge0$, and $p'$ is the strict maximizer of $u_1u_2$ over $S'$ in the closed first quadrant.
--
--   Nash applies this with $\alpha_i=1/p_i$ (possible because $p_1,p_2>0$), so that the maximizer becomes the point $(1,1)$; the statement is given for arbitrary positive constants, of which that choice is an instance.
--
--   **Formalization Note** The normalization of p. 158 fixes each utility up to multiplication by a positive number; the map $u\mapsto(\alpha_1u_1,\alpha_2u_2)$ with $\alpha_i>0$ is exactly that change of scale.
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), p. 159, Two Person Theory, proof of the assertion ("Let us now choose the utility functions so that the above-mentioned point is transformed into the point (1, 1). Since this involves the multiplication of the utilities by constants, (1, 1) will now be the point of maximum u1 u2.")

import Mathlib

namespace NashBargainingProblem.Axiomatic
theorem nash_point_rescale (S : Set (ℝ × ℝ)) (p : ℝ × ℝ)
    (hp_mem : p ∈ S) (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2)
    (hp_max : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2)
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    let S' := (fun u : ℝ × ℝ => (α₁ * u.1, α₂ * u.2)) '' S
    let p' : ℝ × ℝ := (α₁ * p.1, α₂ * p.2)
    p' ∈ S' ∧ 0 ≤ p'.1 ∧ 0 ≤ p'.2 ∧
      ∀ s ∈ S', 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p' → s.1 * s.2 < p'.1 * p'.2 := by sorry
end NashBargainingProblem.Axiomatic
