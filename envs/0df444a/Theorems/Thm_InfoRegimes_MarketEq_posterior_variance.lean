-- Prove2me | Theorems.Thm_InfoRegimes_MarketEq_posterior_variance
-- name    : InfoRegimes.MarketEq.posterior_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:47.316417+00:00
-- url     : https://prove2.me/theorems/c8dd2fa5-2058-4e89-ae3e-8373255c4643
-- title:
--   Footnote 32, p. 42 — with K = cov(m,P)/var(P) for P = bm − cX: K = b var(m)/(b²var(m) + c²var(X)) and var(m − KP) = (1 − Kb)var(m)
-- statement:
--   Let $m$ and $X$ be independent, square-integrable real random variables on a probability space, and let $b, c \in \mathbb R$ with $b^2\operatorname{var}(m) + c^2\operatorname{var}(X) > 0$. Put $P = bm - cX$ and let $K = \operatorname{cov}(m, P)/\operatorname{var}(P)$ be the regression coefficient of $m$ on $P$. Then
--   $$K = \frac{b\operatorname{var}(m)}{b^2\operatorname{var}(m) + c^2\operatorname{var}(X)}\qquad\text{and}\qquad \operatorname{var}(m - KP) = (1 - Kb)\operatorname{var}(m).$$
--
--   With $m = m_t$ (variance $\phi f_t\sigma_M^2$) and $X = X_t$ (variance $\sigma_X^2$), this is the computation behind the uninformed investor's posterior variance (B.7) and gain (B.8): $\operatorname{var}(m_t\mid P_t,\theta_t) = \phi f_t\sigma_M^2(1 - K_tb_t)$.
--
--   **Formalization Note.** The footnote writes $P = bm + cX$; (B.7) uses $bm - cX$, and the statement follows (B.7). The identity is the same for both signs. The variances are Mathlib's `variance`, and no normality or zero mean is assumed: the footnote's computation uses only independence and second moments.
-- source:
--   Glasserman, Mamaysky & Shen, Dynamic Information Regimes in Financial Markets, SSRN 3324789 (version of October 17, 2023), p. 42, footnote 32 (to eqs. (B.7)–(B.8))

import Mathlib

namespace InfoRegimes.MarketEq

open MeasureTheory ProbabilityTheory

theorem posterior_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m X : Ω → ℝ) (hm : MemLp m 2 μ) (hX : MemLp X 2 μ)
    (hind : IndepFun m X μ) (b c : ℝ)
    (hden : 0 < b ^ 2 * variance m μ + c ^ 2 * variance X μ) :
    let Pr : Ω → ℝ := fun ω => b * m ω - c * X ω
    let K : ℝ := covariance m Pr μ / variance Pr μ
    K = b * variance m μ / (b ^ 2 * variance m μ + c ^ 2 * variance X μ) ∧
      variance (fun ω => m ω - K * Pr ω) μ = (1 - K * b) * variance m μ := by sorry

end InfoRegimes.MarketEq
