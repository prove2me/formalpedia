-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_lp82_optimal
-- name    : MatousekLP.ZeroSum.lp82_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:17:35.075607+00:00
-- url     : https://prove2.me/theorems/e6ab51ad-aa70-4faa-a64c-e3bcffecd099
-- title:
--   Eq. (8.3) — an optimal solution of (8.2) is a worst-case optimal strategy of Alice
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix, $m, n \ge 1$, and consider the linear program (8.2)
--   $$
--   \text{maximize } x_0 \quad\text{subject to}\quad M^T\mathbf x - \mathbf 1 x_0 \ge \mathbf 0,\quad \sum_{i=1}^m x_i = 1,\quad \mathbf x \ge \mathbf 0 .
--   $$
--   If $(\tilde x_0, \tilde{\mathbf x})$ is an optimal solution of (8.2), then $\tilde{\mathbf x}$ is a mixed strategy of Alice and
--   $$
--   \tilde x_0 = \beta(\tilde{\mathbf x}) = \max_{\mathbf x}\beta(\mathbf x), \tag{8.3}
--   $$
--   the maximum being over all mixed strategies of Alice. In particular $\tilde{\mathbf x}$ is worst-case optimal.
--
--   **Formalization Note** $\max_{\mathbf x}\beta(\mathbf x) = \beta(\tilde{\mathbf x})$ is stated as $\beta(\mathbf x) \le \beta(\tilde{\mathbf x})$ for every mixed strategy $\mathbf x$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 138, Eq. (8.2) and Eq. (8.3)

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game
import Definitions.Def_MatousekLP_ZeroSum_GameLP

namespace MatousekLP.ZeroSum

theorem lp82_optimal {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) (x₀ : ℝ) (xt : Fin m → ℝ) (h : LP82Optimal M x₀ xt) :
    x₀ = beta M xt ∧ xt ∈ stdSimplex ℝ (Fin m) ∧
      ∀ x ∈ stdSimplex ℝ (Fin m), beta M x ≤ beta M xt := by sorry

end MatousekLP.ZeroSum
