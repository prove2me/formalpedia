-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_minimax_equality
-- name    : MatousekLP.ZeroSum.minimax_equality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:16:58.893143+00:00
-- url     : https://prove2.me/theorems/ce4c5661-1af6-4cdf-ba06-d7ae0c9ad44b
-- title:
--   §8.1, p. 137 — max_x min_y xᵀMy = min_y max_x xᵀMy
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix of a zero-sum game with $m, n \ge 1$. Then
--   $$
--   \max_{\mathbf x}\min_{\mathbf y}\mathbf x^T M \mathbf y = \min_{\mathbf y}\max_{\mathbf x}\mathbf x^T M \mathbf y ,
--   $$
--   where $\mathbf x$ ranges over the mixed strategies of Alice and $\mathbf y$ over those of Bob. Both outer optima are attained: there is a number $v$ that is the largest value of $\beta(\mathbf x) = \min_{\mathbf y}\mathbf x^T M\mathbf y$ over mixed $\mathbf x$ and the smallest value of $\alpha(\mathbf y) = \max_{\mathbf x}\mathbf x^T M\mathbf y$ over mixed $\mathbf y$.
--
--   This equality is what gives the minimax theorem its name.
--
--   **Formalization Note** Stated as: there is $v$ that is the greatest element of $\{\beta(\mathbf x)\}$ and the least element of $\{\alpha(\mathbf y)\}$, over mixed strategies.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 137, §8.1 (display after Theorem 8.1.3)

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game

namespace MatousekLP.ZeroSum

theorem minimax_equality {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ v : ℝ, IsGreatest (beta M '' stdSimplex ℝ (Fin m)) v ∧
      IsLeast (alpha M '' stdSimplex ℝ (Fin n)) v := by sorry

end MatousekLP.ZeroSum
