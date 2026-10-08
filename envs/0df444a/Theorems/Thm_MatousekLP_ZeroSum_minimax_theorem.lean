-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_minimax_theorem
-- name    : MatousekLP.ZeroSum.minimax_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:17:13.460571+00:00
-- url     : https://prove2.me/theorems/4dd3e787-a358-40d4-bfe0-9eb690ad88ac
-- title:
--   Theorem 8.1.3 — minimax theorem for zero-sum games
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix of a zero-sum game between Alice ($m \ge 1$ pure strategies) and Bob ($n \ge 1$ pure strategies), and let $\beta(\mathbf x) = \min_{\mathbf y}\mathbf x^T M \mathbf y$ and $\alpha(\mathbf y) = \max_{\mathbf x}\mathbf x^T M \mathbf y$, the optima being over mixed strategies. Then:
--
--   1. Alice has a worst-case optimal mixed strategy $\tilde{\mathbf x}$, i.e. $\beta(\tilde{\mathbf x}) = \max_{\mathbf x}\beta(\mathbf x)$;
--   2. Bob has a worst-case optimal mixed strategy $\tilde{\mathbf y}$, i.e. $\alpha(\tilde{\mathbf y}) = \min_{\mathbf y}\alpha(\mathbf y)$;
--   3. if $\tilde{\mathbf x}$ is any worst-case optimal mixed strategy of Alice and $\tilde{\mathbf y}$ any worst-case optimal mixed strategy of Bob, then $(\tilde{\mathbf x}, \tilde{\mathbf y})$ is a mixed Nash equilibrium;
--   4. there is a real number $v$ such that for all worst-case optimal mixed strategies $\tilde{\mathbf x}$ of Alice and $\tilde{\mathbf y}$ of Bob
--   $$
--   \beta(\tilde{\mathbf x}) = \tilde{\mathbf x}^T M \tilde{\mathbf y} = \alpha(\tilde{\mathbf y}) = v .
--   $$
--
--   The number $v$ is the **value** of the game. The theorem says that "prepare for the worst" is an optimal policy in a zero-sum game: against a worst-case optimal strategy of the opponent, no player can do better than the value.
--
--   **Formalization Note** The book's clause that worst-case optimal strategies "can be efficiently computed by linear programming" is algorithmic and is not part of the formal statement. Clause 4 expresses "the number $\beta(\tilde{\mathbf x}) = \tilde{\mathbf x}^T M \tilde{\mathbf y} = \alpha(\tilde{\mathbf y})$ is the same for all possible worst-case optimal mixed strategies" as a single $v$ chosen before the strategies. The hypotheses $m, n \ge 1$ are the book's standing assumption of §8.1.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 136, Theorem 8.1.3 (Minimax theorem for zero-sum games)

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game

namespace MatousekLP.ZeroSum

theorem minimax_theorem {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) :
    (∃ xt : Fin m → ℝ, IsWorstCaseOptimalAlice M xt) ∧
    (∃ yt : Fin n → ℝ, IsWorstCaseOptimalBob M yt) ∧
    (∀ (xt : Fin m → ℝ) (yt : Fin n → ℝ), IsWorstCaseOptimalAlice M xt →
      IsWorstCaseOptimalBob M yt → IsMixedNash M xt yt) ∧
    ∃ v : ℝ, ∀ (xt : Fin m → ℝ) (yt : Fin n → ℝ), IsWorstCaseOptimalAlice M xt →
      IsWorstCaseOptimalBob M yt →
        beta M xt = v ∧ payoff M xt yt = v ∧ alpha M yt = v := by sorry

end MatousekLP.ZeroSum
