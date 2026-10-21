-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_mean_variance_demand
-- name    : InfoRegimes.MarketEq.mean_variance_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:44.658011+00:00
-- url     : https://prove2.me/theorems/912e7cdd-a582-4f03-82b2-f31d7cfa18ad
-- title:
--   (B.4), p. 42 — the mean-variance objective qq_N − (γ/2)q²q_D is maximized exactly at q = q_N/(γq_D)
-- statement:
--   Let $\gamma > 0$ be a risk aversion parameter, $q_D > 0$ the expected conditional variance of the net profit per share, and $q_N \in \mathbb R$ its conditional expectation. The mean-variance objective
--   $$q \mapsto q\,q_N - \frac{\gamma}{2}q^2 q_D$$
--   attains its maximum over $q \in \mathbb R$ at $q$ if and only if
--   $$q = \frac{1}{\gamma}\,\frac{q_N}{q_D}.$$
--
--   This is the first-order condition (B.4) of the investor problem (B.1): the optimal demand of each investor type is its expected net profit divided by $\gamma$ times its expected conditional variance. It identifies the maximizers required by market clearing in the model with the demand formulas (B.6).
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 42, eq. (B.4)

import Mathlib

namespace InfoRegimes.MarketEq

theorem mean_variance_demand (γ qD qN q : ℝ) (hγ : 0 < γ) (hqD : 0 < qD) :
    IsMaxOn (fun x : ℝ => x * qN - γ / 2 * x ^ 2 * qD) Set.univ q ↔ q = qN / (γ * qD) := by sorry

end InfoRegimes.MarketEq
