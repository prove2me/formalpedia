-- Prove2me | Theorems.Thm_NashBargainingProblem_Axiomatic_exists_enclosing_square
-- name    : NashBargainingProblem.Axiomatic.exists_enclosing_square
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:43.513683+00:00
-- url     : https://prove2.me/theorems/5f09b989-bbfe-44b9-9d46-f4d71d3fa28c
-- title:
--   p. 159 — a square under u₁ + u₂ = 2, symmetric in u₁ = u₂, encloses S
-- statement:
--   For $h>0$ let
--
--   $$
--   Q_h=\{u\in\mathbb R^2 : 2-2h\le u_1+u_2\le 2,\ |u_1-u_2|\le h\}.
--   $$
--
--   In the rotated coordinates $(u_1+u_2)/\sqrt2$ and $(u_1-u_2)/\sqrt2$ this is a square of side $\sqrt2\,h$; it lies in the region $u_1+u_2\le2$, it is symmetric with respect to the line $u_1=u_2$, and one of its sides, $\{u_1+u_2=2,\ |u_1-u_2|\le h\}$, lies on the line $u_1+u_2=2$ and passes through $(1,1)$.
--
--   Let $S\subseteq\mathbb R^2$ be compact with $u_1+u_2\le2$ for all $u\in S$. Then there is $h>0$ such that $S\subseteq Q_h$; moreover $Q_h$ is compact and convex, and $(a,b)\in Q_h$ if and only if $(b,a)\in Q_h$.
--
--   This is the square Nash builds around the set of alternatives, after the previous step has shown that the set lies under the line $u_1+u_2=2$.
--
--   **Formalization Note** The paper's "a square in the region $u_1+u_2\leqslant2$ which is symmetrical in the line $u_1=u_2$, which has one side on the line $u_1+u_2=2$" is the explicit set $Q_h$. Compactness, convexity and the literal symmetry $(a,b)\in Q_h\iff(b,a)\in Q_h$ are stated as conclusions because the next steps use the square as a bargaining problem and apply the symmetry axiom to it.
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), p. 159, Two Person Theory, proof of the assertion ("We may now construct a square in the region u1 + u2 ⩽ 2 which is symmetrical in the line u1 = u2, …")

import Mathlib

namespace NashBargainingProblem.Axiomatic
theorem exists_enclosing_square (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_le : ∀ u ∈ S, u.1 + u.2 ≤ 2) :
    ∃ h : ℝ, 0 < h ∧
      S ⊆ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      IsCompact {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      Convex ℝ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      (∀ a b : ℝ,
        (a, b) ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ↔
        (b, a) ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}) := by sorry
end NashBargainingProblem.Axiomatic
