-- Prove2me | Theorems.Thm_LinearPriceRule_Concave_linear_price
-- name    : LinearPriceRule.Concave.linear_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:00.209641+00:00
-- url     : https://prove2.me/theorems/d400b0da-5cbe-4e40-9fab-10efa893c8dd
-- title:
--   §1.4, eq. (1), p. 4 — under linear inverse demand P_m − bQ the optimal quantity is (P_m − c)/2b and the price is (P_m + c)/2
-- statement:
--   Let $P_m > c$ and $b > 0$, and suppose the inverse demand is linear, $P(Q) = P_m - bQ$, so that selling $Q \ge 0$ units earns $(P_m - bQ - c)\,Q$. Then the profit is maximized over $Q \ge 0$ uniquely at
--   $$
--   Q^*_L = \frac{P_m - c}{2b}, \qquad\text{with price}\qquad P_m - b\,Q^*_L = \frac{P_m + c}{2}.
--   $$
--
--   This is the source of the pricing rule: the profit-maximizing price under a linear demand does not depend on the slope $b$, so a firm that knows only $P_m$ and $c$ can charge $P^* = (P_m + c)/2$ (the "linear price") without knowing $b$.
--
--   **Formalization Note** The statement asserts that $Q^*_L$ is a maximizer on $[0, \infty)$, that it is the only one, and the identity for the price. No sign condition on $c$ is needed here.
-- source:
--   Cohen, Perakis & Pindyck, SSRN 2673810, p. 4, §1.4, eq. (1)

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

namespace LinearPriceRule.Concave
theorem linear_price (Pm b c : ℝ) (hb : 0 < b) (hc : c < Pm) :
    IsMaxOn (linProfitAt Pm b c) (Set.Ici 0) ((Pm - c) / (2 * b)) ∧
    (∀ Q ∈ Set.Ici (0 : ℝ), IsMaxOn (linProfitAt Pm b c) (Set.Ici 0) Q →
      Q = (Pm - c) / (2 * b)) ∧
    Pm - b * ((Pm - c) / (2 * b)) = (Pm + c) / 2 := by sorry
end LinearPriceRule.Concave
