-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_dual81_value
-- name    : MatousekLP.ZeroSum.dual81_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:17:15.877186+00:00
-- url     : https://prove2.me/theorems/dde86c48-1dfb-474e-8411-b77ac3be0161
-- title:
--   §8.1, p. 137 — the dual of (8.1) has optimal value β(x)
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix, $m, n \ge 1$, and let $\mathbf x$ be a mixed strategy of Alice. The value $\beta(\mathbf x) = \min_{\mathbf y}\mathbf x^T M\mathbf y$ is the optimal value of the linear program (8.1): minimize $\mathbf x^T M \mathbf y$ subject to $\sum_{j=1}^n y_j = 1$, $\mathbf y \ge \mathbf 0$. Its dual is the one-variable program
--   $$
--   \text{maximize } x_0 \quad\text{subject to}\quad M^T\mathbf x - \mathbf 1 x_0 \ge \mathbf 0 ,
--   $$
--   and its optimal value is again $\beta(\mathbf x)$: the number $\beta(\mathbf x)$ is feasible for this dual program, and every feasible $x_0$ satisfies $x_0 \le \beta(\mathbf x)$.
--
--   This identity is what allows the maximization of the nonlinear function $\beta$ over Alice's mixed strategies to be written as the linear program (8.2).
--
--   **Formalization Note** "Optimal value" is stated as `IsGreatest` of the feasible set of the dual program, so the statement includes that the maximum is attained.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 137, §8.1, proof of Theorem 8.1.3 (the dual of the linear program (8.1))

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game
import Definitions.Def_MatousekLP_ZeroSum_GameLP

namespace MatousekLP.ZeroSum

theorem dual81_value {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (hx : x ∈ stdSimplex ℝ (Fin m)) :
    IsGreatest {x₀ : ℝ | DualLP81Feasible M x x₀} (beta M x) := by sorry

end MatousekLP.ZeroSum
