-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_selfConsistent_marketEquilibrium
-- name    : InfoRegimes.MarketEq.selfConsistent_marketEquilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:35.658973+00:00
-- url     : https://prove2.me/theorems/da4ef670-0dd2-438d-bc1a-de719a585c4b
-- title:
--   §4.1, p. 22 and (B.13)–(B.18), p. 43 — the recipe's coefficients clear the market, and a fixed point of V_B ↦ (26) gives a market equilibrium
-- statement:
--   Assume the standing assumptions, a fraction informed $\lambda(\cdot)$ with values in $[0,1]$, and a conjectured variance $V_B(\cdot) > 0$. Let $b(\cdot), c(\cdot)$ be computed from $V_B$ and $\lambda$ by the steps (B.13)–(B.18), and let $d = \rho/(R-\rho)$, $g = 1/(R-\rho)$. Then:
--
--   1. there is a function $a(\cdot)$ such that the price process $P_t = a(f_t) + b(f_t)m_t + g\theta_t - c(f_t)X_t + dD_t$ clears the market with optimal demands at every state and every realization;
--   2. if $V_B$ is a fixed point of the self-consistency map,
--   $$V_B(f) = b(f)^2\phi f\sigma_M^2 + g^2(1-\phi)f\sigma_M^2 + c(f)^2\sigma_X^2\quad\text{for all } f,$$
--   then a market equilibrium for $\lambda$ exists.
--
--   This is the reduction of p. 22: given a conjectured variance, Lemma 4.1 yields a price process whose coefficients are those of (B.13)–(B.18); a self-consistent $V_B$ is a fixed point of the map from conjectures to recomputed variances; and once one is found, Lemma 4.1 delivers a market equilibrium.
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 22, §4.1 (paragraph after (26)); p. 43, eqs. (B.13)–(B.18)

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace InfoRegimes.MarketEq

theorem selfConsistent_marketEquilibrium (P : Params) (hS : P.Standing) (lam : State P → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) (VB : State P → ℝ) (hVB : ∀ i, 0 < VB i) :
    (∃ C : PriceCoeffs P, C.b = bRec P lam VB ∧ C.c = cRec P lam VB ∧
        C.d = dConst P ∧ C.g = gConst P ∧ Clears P lam VB C) ∧
      (Tmap P lam VB = VB → MarketEquilibrium P lam) := by sorry

end InfoRegimes.MarketEq
