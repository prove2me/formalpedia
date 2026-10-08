-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_weak_minimax
-- name    : MatousekLP.ZeroSum.weak_minimax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:16:26.484253+00:00
-- url     : https://prove2.me/theorems/249a29c1-36fd-4d20-a394-d44132d69561
-- title:
--   Lemma 8.1.2(i) — β(x) ≤ xᵀMy ≤ α(y), hence max β ≤ min α
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix of a zero-sum game, $m, n \ge 1$, and let $\beta(\mathbf x) = \min_{\mathbf y}\mathbf x^T M\mathbf y$ and $\alpha(\mathbf y) = \max_{\mathbf x}\mathbf x^T M \mathbf y$. Then
--
--   1. $\beta(\mathbf x) \le \alpha(\mathbf y)$ for all mixed strategies $\mathbf x$ of Alice and $\mathbf y$ of Bob, that is, $\max_{\mathbf x}\beta(\mathbf x) \le \min_{\mathbf y}\alpha(\mathbf y)$;
--   2. for every two mixed strategies $\mathbf x$ and $\mathbf y$,
--   $$
--   \beta(\mathbf x) \le \mathbf x^T M \mathbf y \le \alpha(\mathbf y).
--   $$
--
--   This is the game-theoretic analogue of weak LP duality; the minimax theorem upgrades part 1 to an equality.
--
--   **Formalization Note** The book's $\max_{\mathbf x}\beta(\mathbf x) \le \min_{\mathbf y}\alpha(\mathbf y)$ is stated as $\beta(\mathbf x) \le \alpha(\mathbf y)$ for all mixed $\mathbf x, \mathbf y$, which is equivalent and does not presuppose that the maximum and minimum exist.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 135, Lemma 8.1.2(i)

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game

namespace MatousekLP.ZeroSum

theorem weak_minimax {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x ∈ stdSimplex ℝ (Fin m), ∀ y ∈ stdSimplex ℝ (Fin n), beta M x ≤ alpha M y) ∧
    (∀ x ∈ stdSimplex ℝ (Fin m), ∀ y ∈ stdSimplex ℝ (Fin n),
      beta M x ≤ payoff M x y ∧ payoff M x y ≤ alpha M y) := by sorry

end MatousekLP.ZeroSum
