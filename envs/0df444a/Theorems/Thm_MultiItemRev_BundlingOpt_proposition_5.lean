-- Prove2me | Theorems.Thm_MultiItemRev_BundlingOpt_proposition_5
-- name    : MultiItemRev.BundlingOpt.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:37.215462+00:00
-- url     : https://prove2.me/theorems/ba82b3d8-7d4f-4988-9e76-d21179be1f30
-- title:
--   Proposition 5, p. 13 — IC iff the buyer payoff b is convex with q(x) a subgradient at x
-- statement:
--   Let $\mu = (q, s)$ be a mechanism for $k \ge 1$ goods with buyer payoff $b(x) = q(x)\cdot x - s(x)$ on $\mathbb{R}^k_+$. Then $\mu$ is incentive compatible if and only if $b$ is a convex function on $\mathbb{R}^k_+$ and, for every $x$, the vector $q(x)$ is a subgradient of $b$ at $x$:
--   $$b(\tilde x) - b(x) \ \ge\ q(x)\cdot(\tilde x - x) \qquad \text{for all } x, \tilde x \in \mathbb{R}^k_+.$$
--
--   This is Rochet's characterization of incentive compatibility; it lets revenue be expressed through the convex function $b$ alone.
--
--   **Formalization Note** Convexity on the cone $\mathbb{R}^k_+$ is stated directly: $b(t x + (1-t) y) \le t\,b(x) + (1-t)\,b(y)$ for all $x, y \in \mathbb{R}^k_+$ and $t \in [0,1]$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 13, Proposition 5

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

theorem proposition_5 {ι : Type*} [Fintype ι] [Nonempty ι] (M : Mechanism ι) :
    IsIC M ↔
      ((∀ (x y : ι → ℝ≥0) (t : ℝ≥0), t ≤ 1 →
          buyerPayoff M (t • x + (1 - t) • y) ≤
            (t : ℝ) * buyerPayoff M x + (1 - (t : ℝ)) * buyerPayoff M y) ∧
        ∀ x x' : ι → ℝ≥0,
          ∑ i, M.q x i * ((x' i : ℝ) - (x i : ℝ)) ≤ buyerPayoff M x' - buyerPayoff M x) := by sorry

end MultiItemRev.BundlingOpt
