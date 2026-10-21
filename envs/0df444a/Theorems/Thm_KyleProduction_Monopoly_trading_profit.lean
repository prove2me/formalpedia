-- Prove2me | Theorems.Thm_KyleProduction_Monopoly_trading_profit
-- name    : KyleProduction.Monopoly.trading_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:51.925791+00:00
-- url     : https://prove2.me/theorems/8b9b6228-f888-4d87-8041-8b62bd530cf2
-- title:
--   Appendix A, proof of Proposition 1, (33), p. 24 (PDF 25) — in every linear trading equilibrium E[Π] = (|q|/2)√(ΣuΣaΣθ/(Σa+Σθ))
-- statement:
--   Let $q \in \mathbb R$ be any output quantity and let $(\alpha,\beta,\mu,\lambda)$ be any linear equilibrium of the trading stage at $q$. Then the manager's expected trading profit, before $\tilde a$ is known, is
--   $$E\big[(\tilde V - p)\,d\big] = \frac{|q|}{2}\sqrt{\frac{\Sigma_u\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}} .$$
--
--   The insider's expected gain grows linearly with the scale of production, because production scales the uncertainty of the firm value. This is the force that leads the manager to overproduce in Proposition 1.
--
--   **Formalization Note.** The page has $\hat q > 0$ in mind and writes $\hat q/2$. The production stage compares against every real quantity, including negative ones (footnote 7), so the statement is given with $|q|$. At $q = 0$ the firm value is identically $0$ and every linear equilibrium has profit $0$. The bracket of (33) is printed as $(\hat q(\tilde a-\hat q)) - \hat q(a - \hat q)$; it should read $\hat q(\tilde a - \hat q) - \hat q(E[a|s]-\hat q)$, the firm value minus its mean. Only the stated value is formalized.
-- source:
--   Chen and Jorgensen, Insider Trading, Competition, and Real Activities Manipulation, SSRN 2358668 (version of February 2016), p. 24 (PDF 25), Appendix A, proof of Proposition 1, (33) and the sentence after it

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

namespace KyleProduction.Monopoly

theorem trading_profit (P : Params) (hS : P.Standing) (q : ℝ) (e : LinStrat)
    (he : IsLinEq P q e) :
    tradingProfit P q e = |q| / 2 * kappa P := by sorry

end KyleProduction.Monopoly
