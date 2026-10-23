-- Prove2me | Theorems.Thm_LinearPriceRule_Concave_proposition_5
-- name    : LinearPriceRule.Concave.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:05.702776+00:00
-- url     : https://prove2.me/theorems/293d033f-8cf5-4940-9128-147dd8234f83
-- title:
--   Proposition 5, p. 13 — for concave inverse demand, 1 ≤ Π**/Π* ≤ 2 and 1 ≤ P**/P* ≤ 2 for the linear price P* = (P_m + c)/2
-- statement:
--   Consider a monopoly with maximum price $P_m$, marginal cost $0 \le c < P_m$, saturation quantity $Q_{\max} > 0$, and an inverse demand $P_A$ with $P_A(0) = P_m$ that is non-increasing, continuous and **concave** on $[0, Q_{\max}]$. Let $P^* = (P_m + c)/2$ be the linear price, $\Pi^* = (P^* - c)\,Q_A(P^*)$ the profit of charging it, where $Q_A(p)$ is the largest quantity in $[0, Q_{\max}]$ with $P_A(Q) \ge p$. Then a profit-maximizing quantity exists, $\Pi^* > 0$, and every profit-maximizing quantity $Q^{**}$, with optimal price $P^{**} = P_A(Q^{**})$ and optimal profit $\Pi^{**} = (P^{**} - c)\,Q^{**}$, satisfies
--   $$
--   1 \le \frac{\Pi^{**}}{\Pi^*} \le 2, \qquad 1 \le \frac{P^{**}}{P^*} \le 2.
--   $$
--
--   The linear pricing rule needs only $P_m$ and $c$. For every concave inverse demand it earns at least half of the optimal profit, and the factor $2$ is attained by a rectangular demand.
--
--   **Formalization Note** The paper says "concave demand curve"; its proof invokes Theorem 1, which is about the inverse demand $P_A$, so concavity is of $P_A$ in $Q$ (footnote 6, p. 8, notes that concave $P_A$ gives concave demand). Existence of an optimum and $\Pi^* > 0$ are asserted so that the ratios are well defined; the bounds hold for every maximizer. Ratios are real divisions.
-- source:
--   Cohen, Perakis & Pindyck, SSRN 2673810, p. 13, Proposition 5 (proof p. 26)

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

namespace LinearPriceRule.Concave
theorem proposition_5 (M : Market) (hM : M.Standing)
    (hconc : ConcaveOn ℝ (Set.Icc 0 M.Qmax) M.PA) :
    (∃ Q, IsOptQty M Q) ∧ 0 < linProfit M ∧
    ∀ Q, IsOptQty M Q →
      (1 ≤ profit M Q / linProfit M ∧ profit M Q / linProfit M ≤ 2) ∧
      (1 ≤ M.PA Q / linPrice M ∧ M.PA Q / linPrice M ≤ 2) := by sorry
end LinearPriceRule.Concave
