-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_eq_A9_indifference
-- name    : MarketFreeze.Hetero.eq_A9_indifference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:46.695234+00:00
-- url     : https://prove2.me/theorems/3793c1f3-8e91-4b96-83ff-b1732adf870b
-- title:
--   (A9) and (15), p. 37 — buyers and sellers earn the same iff (A9) holds iff (15) holds
-- statement:
--   For a boom probability $\theta\in[0,\bar\theta]$ and positive buyer/seller ratio $n$, a buyer and seller earn equal profits exactly when the paper's indifference equation (A9) holds. Substituting the matching probability and Nash price gives
--
--   $$\lambda(X-I)\left[\frac{1-\theta}{2}\frac{n-1}{n+1}-\frac{\psi}{(n+1)^2}\right]=\Delta\pi^{\mathrm{hom}}(\theta).$$
--
--   This is equation (15), which determines market tightness in an interior heterogeneous equilibrium. Both versions of the equation are asserted equivalent to profit equality.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), equations (A9) and (15), p. 37

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem eq_A9_indifference (P : Params) (h0 : Standing P)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 P.θbar) (n : ℝ) (hn : 0 < n) :
    (buyerProfit P θ n = sellerProfit P θ n ↔
      alpha P n * ((1 - θ) / 2 *
        (price P n - P.I - (P.X - price P n) / n) -
        P.ψ * (P.X - price P n) / n) = dPi P θ) ∧
    (buyerProfit P θ n = sellerProfit P θ n ↔ eq15LHS P θ n = dPi P θ) := by sorry

end MarketFreeze.Hetero
