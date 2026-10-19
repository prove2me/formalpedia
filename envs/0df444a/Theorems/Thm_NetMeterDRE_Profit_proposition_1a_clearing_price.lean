-- Prove2me | Theorems.Thm_NetMeterDRE_Profit_proposition_1a_clearing_price
-- name    : NetMeterDRE.Profit.proposition_1a_clearing_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:35.253387+00:00
-- url     : https://prove2.me/theorems/e1efa8d1-bb5a-4dd8-ba4f-eb4adb0fac08
-- title:
--   Proposition 1(a), p. 12 (PDF 12), second sentence, and (EC.8) — the equilibrium clearing price is unique, equals α·Dw, and p∗w′ = α
-- statement:
--   Let $N > 2$ and $c > 0$, and let every generator submit the symmetric supply function $S(p) = (N-2)p/((N-1)2c)$. Write $\alpha = 2c(N-1)/((N-2)N)$.
--
--   1. For every realization $\mathcal D_w$ of the net wholesale demand, a price $p$ clears the market, $N\,S(p) = \mathcal D_w$, if and only if
--   $$p = \alpha\,\mathcal D_w .$$
--   2. Consequently, every price function $p^*_w$ that assigns to each $\mathcal D_w$ a market-clearing price has derivative
--   $$p^{*\prime}_w(\mathcal D_w) = \alpha \quad\text{for every } \mathcal D_w .$$
--
--   Part 1 is the second sentence of Proposition 1(a) (the equilibrium market-clearing price is unique for every realization of the net wholesale demand) together with its closed form; part 2 is the identity $\alpha = p^{*\prime}_w(\mathcal D_w)$ used in the proof of Lemma EC.1.
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), p. 12 (PDF 12), Proposition 1(a), second sentence; p. ec4 (PDF 36), (EC.8); p. ec5 (PDF 37), α = p∗w′(Dw)

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE

namespace NetMeterDRE.Profit

theorem proposition_1a_clearing_price (N : ℕ) (c : ℝ) (hN : 2 < N) (hc : 0 < c) :
    (∀ x p : ℝ, IsClearing (fun _ : Fin N => symSupply N c) x p ↔ p = alpha N c * x) ∧
    ∀ pw : ℝ → ℝ, (∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x)) →
      ∀ x₀ : ℝ, deriv pw x₀ = alpha N c := by sorry

end NetMeterDRE.Profit
