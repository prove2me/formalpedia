-- Prove2me | Theorems.Thm_KyleProduction_Monopoly_price_demand
-- name    : KyleProduction.Monopoly.price_demand
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:34.95495+00:00
-- url     : https://prove2.me/theorems/fe64f0c1-a252-4fd3-8806-93b3518b4598
-- title:
--   Appendix A, proof of Proposition 1, (31)–(32), p. 24 (PDF 25) — the equilibrium price and the manager's demand
-- statement:
--   Let $q > 0$, and let the players use the trading-stage equilibrium strategies at $q$. Then for every realization $(a, u)$ the price of the firm's stock is
--   $$p(D) = \frac12\,q\left((E[a|s]-q) + (a-q) + \frac{1}{\Sigma_u}\sqrt{\frac{\Sigma_u\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}}\;u\right),\tag{31}$$
--   and the manager's demand is
--   $$d = -\frac{\sqrt{\Sigma_u}}{\sqrt{\frac{\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}}}(E[a|s]-q) + \frac{\sqrt{\Sigma_u}}{\sqrt{\frac{\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}}}(a-q).\tag{32}$$
--
--   The price puts weight one half on the realized firm value, and the insider buys exactly when demand exceeds its posterior mean.
-- source:
--   Chen and Jorgensen, Insider Trading, Competition, and Real Activities Manipulation, SSRN 2358668 (version of February 2016), p. 24 (PDF 25), Appendix A, proof of Proposition 1, (31)–(32)

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

namespace KyleProduction.Monopoly

theorem price_demand (P : Params) (hS : P.Standing) (q : ℝ) (hq : 0 < q) (a u : ℝ) :
    price (eqStrat P q) (orderFlow (eqStrat P q) q (a, u)) =
      1 / 2 * q * ((postMean P - q) + (a - q) + 1 / P.Su * kappa P * u) ∧
    demand (eqStrat P q) (firmValue q a) =
      -(Real.sqrt P.Su / Real.sqrt (postVar P)) * (postMean P - q) +
        Real.sqrt P.Su / Real.sqrt (postVar P) * (a - q) := by sorry

end KyleProduction.Monopoly
