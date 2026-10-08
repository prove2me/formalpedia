-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_lp84_optimal
-- name    : MatousekLP.ZeroSum.lp84_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:17:24.928517+00:00
-- url     : https://prove2.me/theorems/8d434d32-509e-4513-bca7-e449b33b36c5
-- title:
--   Eq. (8.5) — an optimal solution of (8.4) is a worst-case optimal strategy of Bob
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix, $m, n \ge 1$, and consider the linear program (8.4)
--   $$
--   \text{minimize } y_0 \quad\text{subject to}\quad M\mathbf y - \mathbf 1 y_0 \le \mathbf 0,\quad \sum_{j=1}^n y_j = 1,\quad \mathbf y \ge \mathbf 0 .
--   $$
--   If $(\tilde y_0, \tilde{\mathbf y})$ is an optimal solution of (8.4), then $\tilde{\mathbf y}$ is a mixed strategy of Bob and
--   $$
--   \tilde y_0 = \alpha(\tilde{\mathbf y}) = \min_{\mathbf y}\alpha(\mathbf y), \tag{8.5}
--   $$
--   the minimum being over all mixed strategies of Bob. In particular $\tilde{\mathbf y}$ is worst-case optimal.
--
--   **Formalization Note** $\min_{\mathbf y}\alpha(\mathbf y) = \alpha(\tilde{\mathbf y})$ is stated as $\alpha(\tilde{\mathbf y}) \le \alpha(\mathbf y)$ for every mixed strategy $\mathbf y$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 138, Eq. (8.4) and Eq. (8.5)

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game
import Definitions.Def_MatousekLP_ZeroSum_GameLP

namespace MatousekLP.ZeroSum

theorem lp84_optimal {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) (y₀ : ℝ) (yt : Fin n → ℝ) (h : LP84Optimal M y₀ yt) :
    y₀ = alpha M yt ∧ yt ∈ stdSimplex ℝ (Fin n) ∧
      ∀ y ∈ stdSimplex ℝ (Fin n), alpha M yt ≤ alpha M y := by sorry

end MatousekLP.ZeroSum
