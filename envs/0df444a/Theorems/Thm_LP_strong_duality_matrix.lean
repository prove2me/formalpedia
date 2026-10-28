-- Prove2me | Theorems.Thm_LP_strong_duality_matrix
-- name    : LP.strong_duality_matrix
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:48:24.08391+00:00
-- url     : https://prove2.me/theorems/8a2f2535-07e2-450e-9f00-99374b0548e2
-- title:
--   Linear programming strong duality, with attainment on both sides
-- statement:
--   Let $A$ be a real $m \times n$ matrix, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and suppose both
--
--   $$
--   \exists\, x,\ A x \le b \qquad\text{(primal feasible)} \qquad\text{and}\qquad \exists\, y \ge 0,\ A^{\mathsf T} y = c \qquad\text{(dual feasible)} .
--   $$
--
--   Then there exist $x$ and $y$ with
--
--   $$
--   A x \le b, \qquad y \ge 0, \qquad A^{\mathsf T} y = c, \qquad c \cdot x = b \cdot y,
--   $$
--
--   and $x$ is optimal: $c \cdot x' \le c \cdot x$ for every $x'$ with $A x' \le b$.
--
--   So feasibility of the primal and of the dual is enough: no duality gap, and both optima are
--   *attained*. The equality $c \cdot x = b \cdot y$ is the complementary pair of certificates --
--   $x$ proves that the optimal value is at least $c \cdot x$, and $y$ proves it is at most
--   $b \cdot y$ -- so a single application of this statement supplies both an optimal solution and
--   the proof that it is optimal.
--
--   Attainment is what makes the statement usable inside a larger argument. A reformulation that
--   replaces an inner maximization by its dual minimization needs the dual optimum to be achieved,
--   not merely approached, and that is exactly the content beyond weak duality.
--
--   **Formalization Note** The conclusion is packaged as a single existential over the pair
--   $(x, y)$ together with the optimality clause, so one `obtain` gives everything a caller needs.
--   The proof goes through Farkas' lemma applied to the system that asserts a better objective
--   value than the dual bound allows.
-- source:
--   Carried as an internal support lemma, with this exact statement and proof, in twelve accepted submissions across ten missions of the OR Formalization Drive (e.g. https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1); published here once so that it can be imported. LP strong duality; see Schrijver, Theory of Linear and Integer Programming, Corollary 7.1g, or Bertsimas & Tsitsiklis, Introduction to Linear Optimization, §4.

import Mathlib

open Matrix

namespace LP

theorem strong_duality_matrix {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    (hP : ∃ x, A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c) :
    ∃ x y, A *ᵥ x ≤ b ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ c ⬝ᵥ x = b ⬝ᵥ y ∧
      (∀ x', A *ᵥ x' ≤ b → c ⬝ᵥ x' ≤ c ⬝ᵥ x) := by sorry

end LP
