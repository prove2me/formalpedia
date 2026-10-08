-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_nash_worstCaseOptimal
-- name    : MatousekLP.ZeroSum.nash_worstCaseOptimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:16:38.698262+00:00
-- url     : https://prove2.me/theorems/23dc7f46-dd19-4d5c-8e70-278f21266b95
-- title:
--   Lemma 8.1.2(ii) — both strategies of a mixed Nash equilibrium are worst-case optimal
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix of a zero-sum game, $m, n \ge 1$. If the pair $(\tilde{\mathbf x}, \tilde{\mathbf y})$ of mixed strategies is a mixed Nash equilibrium ($\tilde{\mathbf x}$ is a best response against $\tilde{\mathbf y}$ and $\tilde{\mathbf y}$ is a best response against $\tilde{\mathbf x}$), then $\tilde{\mathbf x}$ is worst-case optimal for Alice and $\tilde{\mathbf y}$ is worst-case optimal for Bob:
--   $$
--   \beta(\tilde{\mathbf x}) = \max_{\mathbf x}\beta(\mathbf x), \qquad \alpha(\tilde{\mathbf y}) = \min_{\mathbf y}\alpha(\mathbf y).
--   $$
--
--   Together with the minimax theorem this gives: a pair of mixed strategies is a Nash equilibrium if and only if both strategies are worst-case optimal.
--
--   **Formalization Note** Worst-case optimality of $\tilde{\mathbf x}$ is stated as: $\tilde{\mathbf x}$ is a mixed strategy and $\beta(\mathbf x) \le \beta(\tilde{\mathbf x})$ for every mixed strategy $\mathbf x$; symmetrically for $\tilde{\mathbf y}$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 136, Lemma 8.1.2(ii)

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game

namespace MatousekLP.ZeroSum

theorem nash_worstCaseOptimal {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) (xt : Fin m → ℝ) (yt : Fin n → ℝ)
    (h : IsMixedNash M xt yt) :
    IsWorstCaseOptimalAlice M xt ∧ IsWorstCaseOptimalBob M yt := by sorry

end MatousekLP.ZeroSum
