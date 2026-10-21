-- Prove2me | Theorems.Thm_KyleProduction_Monopoly_trading_stage
-- name    : KyleProduction.Monopoly.trading_stage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:37.935553+00:00
-- url     : https://prove2.me/theorems/540ce748-2f41-40a8-a5bf-1f2700d2ed1d
-- title:
--   Appendix A, proof of Proposition 1, p. 23 (PDF 24) — for q > 0 the trading stage has the unique linear equilibrium (α, β, µ, λ) of Proposition 1
-- statement:
--   Let $q > 0$. A pair of linear strategies $d(V) = \alpha + \beta V$, $P(y) = \mu + \lambda y$ is a linear equilibrium of the trading stage at $q$ if and only if
--   $$\alpha = -\frac{\sqrt{\Sigma_u}}{\sqrt{\frac{\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}}}(E[a|s]-q),\qquad \beta = \frac{\sqrt{\Sigma_u}}{q\sqrt{\frac{\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}}},$$
--   $$\mu = q\,(E[a|s]-q),\qquad \lambda = \frac{1}{2}\,\frac{q}{\Sigma_u}\sqrt{\frac{\Sigma_u\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}} .$$
--   Here linear equilibrium means two things: the demand is a best response for every realization of $a$, and the price is $E[V\mid D]$.
--
--   This is the one-period Kyle equilibrium for a Gaussian value with variance $q^2\Sigma_a\Sigma_\theta/(\Sigma_a+\Sigma_\theta)$. Existence and uniqueness are both part of the statement.
--
--   **Formalization Note.** The value of $\lambda$ above is the paper's; it equals $\frac{q}{2\sqrt{\Sigma_u}}\sqrt{\Sigma_a\Sigma_\theta/(\Sigma_a+\Sigma_\theta)}$, the form used in the Lean definition. Uniqueness uses $\lambda > 0$, which the page leaves implicit. With $\lambda \le 0$ the insider has no best response for some realization of $a$, so such a pair is never an equilibrium. Nothing has to be assumed for this.
-- source:
--   Chen and Jorgensen, Insider Trading, Competition, and Real Activities Manipulation, SSRN 2358668 (version of February 2016), p. 23 (PDF 24), Appendix A, proof of Proposition 1, last display

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

namespace KyleProduction.Monopoly

theorem trading_stage (P : Params) (hS : P.Standing) (q : ℝ) (hq : 0 < q) (e : LinStrat) :
    IsLinEq P q e ↔ e = eqStrat P q := by sorry

end KyleProduction.Monopoly
