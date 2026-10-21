-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_lemma_4_1
-- name    : InfoRegimes.MarketEq.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:27.253272+00:00
-- url     : https://prove2.me/theorems/f28cb3c0-5b72-405a-9cff-b4feec10c695
-- title:
--   Lemma 4.1, p. 21 — for any V_B > 0 and λ(·) ∈ [0,1], a linear price process (20) with d = ρ/(R−ρ), g = 1/(R−ρ) clears the market
-- statement:
--   Assume the standing assumptions of the model. For any conjectured variance function $V_B(\cdot) > 0$ on the information grid and any fraction informed $\lambda(\cdot)$ taking values in $[0,1]$, there is a linear price process
--   $$P_t = a(f_t) + b(f_t)m_t + g\theta_t - c(f_t)X_t + dD_t,\qquad d = \frac{\rho}{R-\rho},\quad g = \frac{1}{R-\rho},$$
--   such that at every information state and every realization of $(m_t,\theta_t,X_t,D_t)$ the optimal demands $q^I_t, q^U_t$ of the informed and uninformed investors, computed with the conjectured variance $V_B$ as in (25), clear the market:
--   $$\lambda q^I_t + (1-\lambda)q^U_t = \bar X + X_t.$$
--
--   Lemma 4.1 solves the market-clearing problem for a fixed variance conjecture; it is the first half of the existence argument for a market equilibrium, the second being self-consistency of $V_B$.
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 21, Lemma 4.1 (proof: App. B.1, pp. 41–44)

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace InfoRegimes.MarketEq

theorem lemma_4_1 (P : Params) (hS : P.Standing) (VB : State P → ℝ) (hVB : ∀ i, 0 < VB i)
    (lam : State P → ℝ) (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ C : PriceCoeffs P, C.d = P.rho / (P.R - P.rho) ∧ C.g = 1 / (P.R - P.rho) ∧
      Clears P lam VB C := by sorry

end InfoRegimes.MarketEq
