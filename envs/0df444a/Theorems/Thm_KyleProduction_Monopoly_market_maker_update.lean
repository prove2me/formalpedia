-- Prove2me | Theorems.Thm_KyleProduction_Monopoly_market_maker_update
-- name    : KyleProduction.Monopoly.market_maker_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:37.245786+00:00
-- url     : https://prove2.me/theorems/8af5fb99-6d4c-4826-99b2-1d2b0a01bfe4
-- title:
--   Appendix A, proof of Proposition 1, (30), p. 23 (PDF 24) — the price is E[Ṽ | D] iff λ and µ are the Gaussian regression coefficients
-- statement:
--   Fix an output quantity $q$ and linear strategies $d(V) = \alpha + \beta V$ and $P(y) = \mu + \lambda y$. The order flow is $D = \alpha + \beta V + u$, where $V = q(a-q)$ and $u \sim N(0,\Sigma_u)$ are independent. Write $\Sigma_V = q^2\,\Sigma_a\Sigma_\theta/(\Sigma_a+\Sigma_\theta)$ for the variance of $V$.
--
--   The price is efficient, $P(D) = E[V\mid D]$ almost surely (4), if and only if
--   $$\lambda = \frac{\beta\,\Sigma_V}{\beta^2\,\Sigma_V + \Sigma_u}\qquad\text{and}\qquad \mu = q\,(E[a|s]-q) - \lambda\big(\alpha + \beta\,q\,(E[a|s]-q)\big).$$
--
--   This is the market maker's half of the trading stage: since $(V, D)$ is jointly Gaussian, the conditional mean of $V$ given $D$ is affine in $D$, and its coefficients are the ones displayed.
--
--   **Formalization Note.** The paper prints two slips here. The order flow is printed as $\alpha + \beta(\tilde V + \tilde u)$; it is $\alpha + \beta\tilde V + \tilde u$, as in (30) itself and in the variance $\beta^2 q^2(\cdot) + \Sigma_u$ that follows. The denominator of $\lambda$ is printed as $\beta^2\hat q^2\Sigma_a + \Sigma_u$; it is $\beta^2\hat q^2\,\Sigma_a\Sigma_\theta/(\Sigma_a+\Sigma_\theta) + \Sigma_u$, as in the $\mu$ display and the covariance matrix. The corrected forms are stated. The condition holds for every real $q$, $\alpha$, $\beta$, not only at the equilibrium.
-- source:
--   Chen and Jorgensen, Insider Trading, Competition, and Real Activities Manipulation, SSRN 2358668 (version of February 2016), p. 23 (PDF 24), Appendix A, proof of Proposition 1, (30) and the display after it

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

namespace KyleProduction.Monopoly

theorem market_maker_update (P : Params) (hS : P.Standing) (q : ℝ) (e : LinStrat) :
    MarketEfficient P q e ↔
      (e.lam = e.β * q ^ 2 * postVar P / (e.β ^ 2 * q ^ 2 * postVar P + P.Su) ∧
       e.μ = q * (postMean P - q) - e.lam * (e.α + e.β * (q * (postMean P - q)))) := by sorry

end KyleProduction.Monopoly
