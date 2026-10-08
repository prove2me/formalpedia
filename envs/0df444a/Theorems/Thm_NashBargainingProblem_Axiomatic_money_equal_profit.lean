-- Prove2me | Theorems.Thm_NashBargainingProblem_Axiomatic_money_equal_profit
-- name    : NashBargainingProblem.Axiomatic.money_equal_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:21:04.479981+00:00
-- url     : https://prove2.me/theorems/b7a64689-603f-46d0-b37f-f4532e9343ca
-- title:
--   p. 162 — with a common medium of exchange the solution gives each bargainer the same money profit
-- statement:
--   Let $m>0$ and let $S\subseteq\mathbb R^2$ be a set of utility pairs whose part in the closed first quadrant is the isosceles right triangle
--
--   $$
--   \{u\in S : u_1\ge0,\ u_2\ge0\}=\{u : u_1\ge0,\ u_2\ge0,\ u_1+u_2\le m\}.
--   $$
--
--   Then a point $p$ is the strict maximizer of $u_1u_2$ over $S$ in the closed first quadrant (that is, $p\in S$, $p_1,p_2\ge0$, and $s_1s_2<p_1p_2$ for every other $s\in S$ with $s_1,s_2\ge0$) if and only if $p=(m/2,\,m/2)$. Each bargainer gets the same money profit $m/2$.
--
--   This is Nash's last example: when both utilities are measured in money, the frontier in the first quadrant is a line of slope $-1$, and the solution splits the surplus equally.
--
--   **Formalization Note** "An isosceles right triangle" in the first quadrant is read as the triangle with legs on the axes and hypotenuse $u_1+u_2=m$; its slope $-1$ is the common money scale (Figure 3).
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), p. 162, Examples ("When we may use a common medium of exchange … forms an isosceles right triangle. Hence the solution has each bargainer getting the same money profit (see Figure 3).")

import Mathlib

namespace NashBargainingProblem.Axiomatic
theorem money_equal_profit (m : ℝ) (hm : 0 < m) (S : Set (ℝ × ℝ))
    (hS : {u ∈ S | 0 ≤ u.1 ∧ 0 ≤ u.2} = {u : ℝ × ℝ | 0 ≤ u.1 ∧ 0 ≤ u.2 ∧ u.1 + u.2 ≤ m})
    (p : ℝ × ℝ) :
    (p ∈ S ∧ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
      ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2) ↔
    p = (m / 2, m / 2) := by sorry
end NashBargainingProblem.Axiomatic
