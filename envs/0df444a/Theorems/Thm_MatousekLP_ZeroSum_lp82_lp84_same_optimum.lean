-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_lp82_lp84_same_optimum
-- name    : MatousekLP.ZeroSum.lp82_lp84_same_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:17:45.723438+00:00
-- url     : https://prove2.me/theorems/89ca1b96-8cba-42b3-a613-e719b36a3973
-- title:
--   §8.1, p. 138 — the linear programs (8.2) and (8.4) have the same optimum value
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix, $m, n \ge 1$. The linear programs (8.2) (maximize $x_0$ subject to $M^T\mathbf x - \mathbf 1x_0 \ge \mathbf 0$, $\sum_i x_i = 1$, $\mathbf x \ge \mathbf 0$) and (8.4) (minimize $y_0$ subject to $M\mathbf y - \mathbf 1 y_0 \le \mathbf 0$, $\sum_j y_j = 1$, $\mathbf y \ge \mathbf 0$) are dual to each other, and they have the same optimum value:
--
--   1. (8.2) has an optimal solution;
--   2. (8.4) has an optimal solution;
--   3. for every optimal solution $(\tilde x_0, \tilde{\mathbf x})$ of (8.2) and every optimal solution $(\tilde y_0, \tilde{\mathbf y})$ of (8.4),
--   $$
--   \tilde x_0 = \tilde y_0 .
--   $$
--
--   This is the point at which the duality theorem of linear programming enters the proof of the minimax theorem.
--
--   **Formalization Note** "Both programs have the same optimum value" is rendered as the existence of optimal solutions of both programs together with the equality of their objective values; no real supremum over a feasible set is used.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 138, §8.1, proof of Theorem 8.1.3 ("the two linear programs (8.2) and (8.4) are dual to each other … both programs have the same optimum value")

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game
import Definitions.Def_MatousekLP_ZeroSum_GameLP

namespace MatousekLP.ZeroSum

theorem lp82_lp84_same_optimum {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) :
    (∃ (x₀ : ℝ) (x : Fin m → ℝ), LP82Optimal M x₀ x) ∧
    (∃ (y₀ : ℝ) (y : Fin n → ℝ), LP84Optimal M y₀ y) ∧
    ∀ (x₀ : ℝ) (x : Fin m → ℝ) (y₀ : ℝ) (y : Fin n → ℝ),
      LP82Optimal M x₀ x → LP84Optimal M y₀ y → x₀ = y₀ := by sorry

end MatousekLP.ZeroSum
