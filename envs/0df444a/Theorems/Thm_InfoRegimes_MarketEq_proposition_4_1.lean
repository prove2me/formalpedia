-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_proposition_4_1
-- name    : InfoRegimes.MarketEq.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:37.394276+00:00
-- url     : https://prove2.me/theorems/69ff0846-526f-43dc-908c-80a31a8c9052
-- title:
--   Proposition 4.1, p. 22 — if 1 < R ≤ 1.2 and (1+d)γσ_Mσ_X ≤ 0.28, a market equilibrium with linear prices and self-consistent V_B exists for every λ(·)
-- statement:
--   Consider the market with a dynamic information state under the standing assumptions ($R > 1$, $-1 < \rho < 1$, $\sigma_M, \sigma_X, \gamma, \bar X > 0$, $0 \le \phi \le 1$, a grid $\mathcal D = \{0, 1/m, \dots, 1\}$ with $m \ge 1$, and an arbitrary law for the shock $\epsilon_f$ of the information dynamics (6)). Write $d = \rho/(R-\rho)$. Suppose that $R \le 1.2$ and
--   $$(1+d)\gamma\sigma_M\sigma_X = \frac{R\gamma\sigma_M\sigma_X}{R-\rho} \le 0.28. \tag{27}$$
--   Then for every fraction informed $\lambda : \mathcal D \to [0,1]$ there is a market equilibrium: a conjectured variance $V_B > 0$ and a linear price process
--   $$P_t = a(f_t) + b(f_t)m_t + g\theta_t - c(f_t)X_t + dD_t$$
--   such that the optimal demands of informed and uninformed investors clear the market at every information state and every realization of $(m_t,\theta_t,X_t,D_t)$, and $V_B$ is self-consistent,
--   $$V_B(f) = b(f)^2\phi f\sigma_M^2 + g^2(1-\phi)f\sigma_M^2 + c(f)^2\sigma_X^2\quad\text{for all } f\in\mathcal D. \tag{26}$$
--
--   Proposition 4.1 is the paper's existence result for the market stage: it makes the fraction informed a free input, which the information equilibrium of Proposition 4.2 then determines endogenously.
--
--   **Formalization Note.** The page states $R \in [1, 1.2]$; with the standing $R > 1$ of p. 11 this reads $1 < R \le 1.2$. The bound $-1 < \rho < 1$ is added (the paper never states the range of $\rho$). In (27), $d$ is written out as $\rho/(R-\rho)$, and $1.2$ and $0.28$ are written as $6/5$ and $7/25$.
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 22, Proposition 4.1, eq. (27)

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace InfoRegimes.MarketEq

theorem proposition_4_1 (P : Params) (hS : P.Standing) (hR : P.R ≤ 6 / 5)
    (h27 : (1 + P.rho / (P.R - P.rho)) * P.gam * P.sigM * P.sigX ≤ 7 / 25)
    (lam : State P → ℝ) (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) :
    MarketEquilibrium P lam := by sorry

end InfoRegimes.MarketEq
