-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_eq_B19_B21
-- name    : InfoRegimes.MarketEq.eq_B19_B21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:30.989185+00:00
-- url     : https://prove2.me/theorems/b054ff74-e1fe-406a-980d-2be354b4bd16
-- title:
--   (B.19)–(B.21), p. 44 — under clearing, a(·) solves Ra = (1+d)μ_D − γX̄q^Iq^U/(λq^U+(1−λ)q^I) + E_t a and a = (1+d)μ_D/(R−1) − Σ R^{−i}E_t[π_{t+i}]
-- statement:
--   Assume the standing assumptions, a fraction informed $\lambda(\cdot)$ with values in $[0,1]$, a conjectured variance $V_B(\cdot) > 0$, and price coefficients $(a, b, c, d, g)$ whose optimal demands clear the market at every state and realization, with $q^I_D, q^U_D$ as in (B.5). Then at every state $f_t$:
--
--   1. (B.19)
--   $$a_t = \frac{1}{R}\Big[(1+d)\mu_D - \frac{\gamma q^I_Dq^U_D}{\lambda q^U_D + (1-\lambda)q^I_D}\bar X + E_t a(f_{t+1})\Big];$$
--   2. (B.21) with the expected net profit $E_t[\pi_{t+1}] = \pi_1(f_t)$ of (B.20), where $\pi_1(f) = \gamma\bar X\,q^I_D(f)q^U_D(f)/(\lambda(f)q^U_D(f) + (1-\lambda(f))q^I_D(f))$, the series
--   $$\sum_{i=1}^{\infty}\frac{1}{R^i}E_t[\pi_{t+i}],\qquad E_t[\pi_{t+i}] = E_t\,\pi_1(f_{t+i-1}),$$
--   converges, and
--   $$a_t = \frac{(1+d)\mu_D}{R-1} - \sum_{i=1}^{\infty}\frac{1}{R^i}E_t[\pi_{t+i}].$$
--
--   The intercept of the price is the present value of expected dividends minus the present value of the expected net profits that compensate investors for bearing risk.
--
--   **Formalization Note.** Convergence is part of the statement (`HasSum`), so a divergent series cannot hide behind Lean's convention that a non-summable sum is $0$. Conditional expectations $E_t$ are taken under the transition kernel of (6) at the given $\lambda$.
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 44, eqs. (B.19), (B.20), (B.21)

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace InfoRegimes.MarketEq

theorem eq_B19_B21 (P : Params) (hS : P.Standing) (lam : State P → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) (VB : State P → ℝ) (hVB : ∀ i, 0 < VB i)
    (C : PriceCoeffs P) (hC : Clears P lam VB C) (i : State P) :
    C.a i = 1 / P.R * ((1 + C.d) * muD P
        - P.gam * qID P lam VB C i * qUD P lam VB C i
          / (lam i * qUD P lam VB C i + (1 - lam i) * qID P lam VB C i) * P.Xbar
        + Ef P lam i C.a) ∧
      HasSum
        (fun k : ℕ => (P.R ^ (k + 1))⁻¹ * EfIter P lam k
          (fun j => P.gam * P.Xbar * (qID P lam VB C j * qUD P lam VB C j)
            / (lam j * qUD P lam VB C j + (1 - lam j) * qID P lam VB C j)) i)
        ((1 + C.d) * muD P / (P.R - 1) - C.a i) := by sorry

end InfoRegimes.MarketEq
