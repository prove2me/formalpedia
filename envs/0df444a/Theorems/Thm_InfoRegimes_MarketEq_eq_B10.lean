-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_eq_B10
-- name    : InfoRegimes.MarketEq.eq_B10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:29.375986+00:00
-- url     : https://prove2.me/theorems/73d7e231-8086-4ded-add4-5e754a09f875
-- title:
--   (B.10), p. 43 — if optimal demands clear the market, the price constants are d = ρ/(R−ρ) and g = 1/(R−ρ)
-- statement:
--   Assume the standing assumptions of the model, a fraction informed $\lambda(\cdot)$ with values in $[0,1]$, and a conjectured variance $V_B(\cdot) > 0$. If a linear price process
--   $$P_t = a(f_t) + b(f_t)m_t + g\theta_t - c(f_t)X_t + dD_t$$
--   clears the market (11) with optimal demands of the informed and uninformed investors at every state and every realization of $(m_t, \theta_t, X_t, D_t)$, then its constants are
--   $$d = \frac{\rho}{R-\rho}\qquad\text{and}\qquad g = \frac{1}{R-\rho}.$$
--
--   These are the constants of Lemma 4.1; they are forced by collecting the $D_t$ and $\theta_t$ terms of the clearing condition (B.9). The value of $d$ is the one that enters condition (27) of Proposition 4.1.
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 43, eq. (B.10)

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace InfoRegimes.MarketEq

theorem eq_B10 (P : Params) (hS : P.Standing) (lam : State P → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) (VB : State P → ℝ) (hVB : ∀ i, 0 < VB i)
    (C : PriceCoeffs P) (hC : Clears P lam VB C) :
    C.d = P.rho / (P.R - P.rho) ∧ C.g = 1 / (P.R - P.rho) := by sorry

end InfoRegimes.MarketEq
