-- Prove2me | Theorems.Thm_LinearPriceRule_Concave_rectangle_sharp
-- name    : LinearPriceRule.Concave.rectangle_sharp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:03.049656+00:00
-- url     : https://prove2.me/theorems/16888c61-b2d9-4a8b-bc57-e956d8211b5b
-- title:
--   Remark after Proposition 5, p. 13 — for a rectangular demand P_A ≡ P_m the profit ratio Π**/Π* equals 2 (and P**/P* = 2 when c = 0)
-- statement:
--   Consider a market with maximum price $P_m$, marginal cost $0 \le c < P_m$, saturation quantity $Q_{\max} > 0$, and a **rectangular** inverse demand: $P_A(Q) = P_m$ for all $Q \in [0, Q_{\max}]$. Then $Q_{\max}$ is an optimal quantity, and every optimal quantity $Q^{**}$ satisfies
--   $$
--   \frac{\Pi^{**}}{\Pi^*} = 2;
--   $$
--   if moreover $c = 0$, also $P^{**}/P^* = 2$.
--
--   A constant inverse demand is concave, so this shows that the bound $\Pi^{**}/\Pi^* \le 2$ of Proposition 5 is attained.
--
--   **Formalization Note** The paper says "the profit and price ratios will equal 2". The price ratio of the rectangle is $2P_m/(P_m + c)$, which equals $2$ only when $c = 0$; the price part is stated with $c = 0$.
-- source:
--   Cohen, Perakis & Pindyck, SSRN 2673810, p. 13, remark after Proposition 5; rectangle example §1.4, p. 6

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

namespace LinearPriceRule.Concave
theorem rectangle_sharp (M : Market) (hM : M.Standing)
    (hrect : ∀ Q ∈ Set.Icc 0 M.Qmax, M.PA Q = M.Pm) :
    IsOptQty M M.Qmax ∧
    (∀ Q, IsOptQty M Q → profit M Q / linProfit M = 2) ∧
    (M.c = 0 → ∀ Q, IsOptQty M Q → M.PA Q / linPrice M = 2) := by sorry
end LinearPriceRule.Concave
