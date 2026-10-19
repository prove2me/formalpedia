-- Prove2me | Theorems.Thm_KanCombine_Optimal_eq_A13
-- name    : KanCombine.Optimal.eq_A13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:01.117044+00:00
-- url     : https://prove2.me/theorems/15d9033b-a4be-4cb6-8f3b-4c22ba439c5a
-- title:
--   (A13), p. 32 — E[σ_gz,t] = 0: the sample GMV and zero-investment portfolios are uncorrelated on average
-- statement:
--   Let $N \ge 2$ risky assets have returns that are i.i.d. over time and multivariate normal with mean $\mu$ and positive definite covariance $\Sigma$, let $\gamma > 0$, and let $h > N + 3$ be the length of the estimation window. From the $h$ returns form the maximum-likelihood estimators $\hat\mu_t$, $\hat\Sigma_t$, the sample GMV portfolio $\hat w_{g,t} = \hat\Sigma_t^{-1}1_N/(1_N'\hat\Sigma_t^{-1}1_N)$ and the sample zero-investment portfolio $\hat w_{z,t} = \hat\Sigma_t^{-1}(\hat\mu_t - 1_N\hat\mu_{g,t})$. Write $\sigma_g^2 = 1/(1_N'\Sigma^{-1}1_N)$, $\mu_g = 1_N'\Sigma^{-1}\mu\,\sigma_g^2$ and $\psi^2 = \mu'\Sigma^{-1}\mu - \mu_g^2/\sigma_g^2$. Then the out-of-sample covariance $\sigma_{gz,t} = \hat w_{g,t}'\Sigma\hat w_{z,t}$ of the two sample portfolios is integrable and
--   $$E[\sigma_{gz,t}] = 0.$$
--
--   Conditionally on the sample the two portfolios are correlated, but on average the covariance vanishes; this removes the cross term from Lemma 1.
--
--   **Formalization Note** $N \ge 2$, $\Sigma \succ 0$ and $\gamma > 0$ are implicit in the paper and made explicit. The statement asserts integrability as well as the value, because a Lean expectation of a non-integrable quantity is $0$. Lean's matrix inverse is $0$ on singular matrices; $\hat\Sigma_t$ is almost surely nonsingular here, so this does not matter.
-- source:
--   Kan, Wang & Zhou, Optimal portfolio choice with estimation risk: No risk-free asset case, submitted manuscript (version of November 2020; SSRN 2819254, TSpace), p. 32 (PDF 35), proof of Lemma 1, eq. (A13)

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_KanCombine_Optimal_Model

namespace KanCombine.Optimal

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

/-- (A13), p. 32: for h > N + 3, E[σ_{gz,t}] = 0, where σ_{gz,t} = ŵ_{g,t}′Σŵ_{z,t}. -/
theorem eq_A13 {N h : ℕ} (M : Market N) (hM : KanStanding M h)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r) :
    Integrable (fun ω => sigGZt M (sampleData r ω)) P ∧
      ∫ ω, sigGZt M (sampleData r ω) ∂P = 0 := by sorry

end KanCombine.Optimal
