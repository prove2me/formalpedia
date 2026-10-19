-- Prove2me | Theorems.Thm_KanCombine_Optimal_eq_20
-- name    : KanCombine.Optimal.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:59.736669+00:00
-- url     : https://prove2.me/theorems/cf7337a5-49b7-4c52-8452-883ea8b6115d
-- title:
--   §2.3, eqs. (20)–(21), p. 10 — for h > N + 3, c̃* = kψ²/(ψ² + (N−1)/h) uniquely maximizes E[U(ŵ_t(c̃))], and 0 ≤ c̃* < 1
-- statement:
--   Let $N \ge 2$ risky assets have returns that are i.i.d. over time and multivariate normal with mean $\mu$ and positive definite covariance $\Sigma$, let $\gamma > 0$, and let $h > N + 3$ be the length of the estimation window. From the $h$ returns form the maximum-likelihood estimators $\hat\mu_t$, $\hat\Sigma_t$, the sample GMV portfolio $\hat w_{g,t} = \hat\Sigma_t^{-1}1_N/(1_N'\hat\Sigma_t^{-1}1_N)$ and the sample zero-investment portfolio $\hat w_{z,t} = \hat\Sigma_t^{-1}(\hat\mu_t - 1_N\hat\mu_{g,t})$. Write $\sigma_g^2 = 1/(1_N'\Sigma^{-1}1_N)$, $\mu_g = 1_N'\Sigma^{-1}\mu\,\sigma_g^2$ and $\psi^2 = \mu'\Sigma^{-1}\mu - \mu_g^2/\sigma_g^2$. For a constant $\tilde c \in \mathbb R$ let $\hat w_t(\tilde c) = \hat w_{g,t} + \tilde c\,\hat w_{z,t}/\gamma$ and let $E[U(\hat w_t(\tilde c))]$ be its expected out-of-sample utility, the utility $U(w) = w'\mu - \frac\gamma2 w'\Sigma w$ at the true parameters averaged over the estimation sample. Put
--   $$k = \frac{(h-N)(h-N-3)}{h(h-2)}, \qquad \tilde c^* = \frac{k\psi^2}{\psi^2 + \frac{N-1}{h}}.$$
--   Then:
--
--   1. $\tilde c^*$ maximizes the expected out-of-sample utility: $E[U(\hat w_t(\tilde c))] \le E[U(\hat w_t(\tilde c^*))]$ for every $\tilde c \in \mathbb R$;
--   2. it is the only maximizer: equality holds only for $\tilde c = \tilde c^*$;
--   3. $0 \le \tilde c^* < 1$, and $\tilde c^* > 0$ whenever $\psi^2 > 0$.
--
--   The optimal combining portfolio thus accounts for estimation risk by holding strictly less of the sample zero-investment portfolio than the plug-in rule $\tilde c = 1$ does.
--
--   **Formalization Note** The paper states "$0 < \tilde c^* < 1$" for $h > N + 3$; at $\psi^2 = 0$ (that is, $\mu$ proportional to $1_N$, a case the paper discusses on p. 8) one has $\tilde c^* = 0$, so the strict lower bound is stated under $\psi^2 > 0$ and $\tilde c^* \ge 0$ in general. "Maximizes" is read over all real constants $\tilde c$, and "the optimal value" as uniqueness of the maximizer. The statement is about the true expectation over the Gaussian sample, not about the closed-form quadratic (17). $N \ge 2$, $\Sigma \succ 0$ and $\gamma > 0$ are implicit in the paper and made explicit; for $h > N + 3$ the expected utility is a genuine (finite) expectation by Lemma 1.
-- source:
--   Kan, Wang & Zhou, Optimal portfolio choice with estimation risk: No risk-free asset case, submitted manuscript (version of November 2020; SSRN 2819254, TSpace), p. 10 (PDF 13), §2.3, eqs. (20)–(21) and the sentence 'For h > N + 3, it is easy to show that 0 < c̃∗ < 1'

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_KanCombine_Optimal_Model

namespace KanCombine.Optimal

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

/-- §2.3, eqs. (20)–(21), p. 10: for h > N + 3, c̃* = kψ²/(ψ² + (N − 1)/h) is the unique maximizer of the expected out-of-sample utility over constant c̃ ∈ ℝ; moreover 0 ≤ c̃* < 1, and c̃* > 0 when ψ² > 0 (the page's "0 < c̃*", corrected for ψ² = 0). -/
theorem eq_20 {N h : ℕ} (M : Market N) (hM : KanStanding M h)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r) :
    (∀ c : ℝ, expUtility M P r c ≤ expUtility M P r (cStar M h)) ∧
    (∀ c : ℝ, expUtility M P r c = expUtility M P r (cStar M h) → c = cStar M h) ∧
    0 ≤ cStar M h ∧ cStar M h < 1 ∧ (0 < M.psi2 → 0 < cStar M h) := by sorry

end KanCombine.Optimal
