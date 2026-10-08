-- Prove2me | Theorems.Thm_NashBargainingProblem_Axiomatic_square_unique_symmetric_undominated
-- name    : NashBargainingProblem.Axiomatic.square_unique_symmetric_undominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:52.463159+00:00
-- url     : https://prove2.me/theorems/9340a7b7-f256-48f9-bad4-d5ad1dfd454f
-- title:
--   p. 159 — (1, 1) is the only point of the square satisfying assumptions (6) and (8)
-- statement:
--   Let $h>0$ and let $Q_h=\{u\in\mathbb R^2 : 2-2h\le u_1+u_2\le2,\ |u_1-u_2|\le h\}$ be the square of the previous step. For a point $p\in Q_h$ the following are equivalent:
--
--   1. $p$ lies on the line $u_1=u_2$ (what assumption (8) demands of the solution of a symmetric set), and no point $t\in Q_h$ has both $t_1>p_1$ and $t_2>p_2$ (what assumption (6) demands of the solution);
--   2. $p=(1,1)$.
--
--   $$
--   \bigl(p_1=p_2\ \wedge\ \neg\exists t\in Q_h,\ t_1>p_1,\ t_2>p_2\bigr)\iff p=(1,1).
--   $$
--
--   Thus, when the square is taken as the set of alternatives, Nash's assumptions (6) and (8) leave only the point $(1,1)$.
--
--   **Formalization Note** "Satisfying assumption (8)" is read as lying on the diagonal and "satisfying assumption (6)" as not being strictly dominated by a point of the square; the statement is the geometric fact, not a statement about a solution map, which is the business of the last milestone.
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), p. 159, Two Person Theory, proof of the assertion ("Considering the square region formed as the set of alternatives, instead of the older set, it is clear that (1, 1) is the only point satisfying assumptions (6) and (8)."); assumptions 6 and 8, p. 159

import Mathlib

namespace NashBargainingProblem.Axiomatic
theorem square_unique_symmetric_undominated (h : ℝ) (hh : 0 < h) (p : ℝ × ℝ)
    (hp : p ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}) :
    (p.1 = p.2 ∧
      ∀ t ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h},
        ¬ (p.1 < t.1 ∧ p.2 < t.2)) ↔ p = ((1 : ℝ), (1 : ℝ)) := by sorry
end NashBargainingProblem.Axiomatic
