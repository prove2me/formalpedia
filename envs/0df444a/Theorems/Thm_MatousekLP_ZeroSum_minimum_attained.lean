-- Prove2me | Theorems.Thm_MatousekLP_ZeroSum_minimum_attained
-- name    : MatousekLP.ZeroSum.minimum_attained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:16:05.883289+00:00
-- url     : https://prove2.me/theorems/006f7b8c-fb94-47b0-bba3-c9c8b071e97a
-- title:
--   §8.1, p. 135 — β and α are attained minimum and maximum
-- statement:
--   Let $M$ be a real $m \times n$ payoff matrix with $m, n \ge 1$, and let $\beta$, $\alpha$ be the worst-case payoff functions of the zero-sum game $M$. Then for every mixed strategy $\mathbf x$ of Alice the value $\beta(\mathbf x)$ is attained by some mixed strategy of Bob, and for every mixed strategy $\mathbf y$ of Bob the value $\alpha(\mathbf y)$ is attained by some mixed strategy of Alice:
--   $$
--   \beta(\mathbf x) = \min_{\mathbf y} \mathbf x^T M \mathbf y, \qquad \alpha(\mathbf y) = \max_{\mathbf x} \mathbf x^T M \mathbf y .
--   $$
--   Precisely: $\beta(\mathbf x)$ is a lower bound of all values $\mathbf x^T M \mathbf y$ over mixed $\mathbf y$ and equals one of them, and symmetrically for $\alpha(\mathbf y)$.
--
--   This is the book's remark that $\beta$ and $\alpha$ are well-defined because the optimization is over compact sets (the simplices of mixed strategies).
--
--   **Formalization Note** $\beta$ and $\alpha$ are defined as the real `sInf` / `sSup` of the image of the simplex; this theorem is what makes those definitions agree with the book's $\min$ and $\max$. The hypotheses $m, n \ge 1$ are the book's standing assumption; without them a simplex is empty.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 135, §8.1 ("β and α are well-defined functions, since we are optimizing over compact sets")

import Mathlib
import Definitions.Def_MatousekLP_ZeroSum_Game

namespace MatousekLP.ZeroSum

theorem minimum_attained {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x ∈ stdSimplex ℝ (Fin m),
      IsLeast ((fun y => payoff M x y) '' stdSimplex ℝ (Fin n)) (beta M x)) ∧
    (∀ y ∈ stdSimplex ℝ (Fin n),
      IsGreatest ((fun x => payoff M x y) '' stdSimplex ℝ (Fin m)) (alpha M y)) := by sorry

end MatousekLP.ZeroSum
