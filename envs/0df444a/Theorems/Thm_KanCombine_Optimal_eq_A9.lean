-- Prove2me | Theorems.Thm_KanCombine_Optimal_eq_A9
-- name    : KanCombine.Optimal.eq_A9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:51.025068+00:00
-- url     : https://prove2.me/theorems/5013bb36-1bfa-4509-8e69-4750fc6fde05
-- title:
--   (A9), p. 32 — E[µ_g,t] = µ_g: the out-of-sample mean of the sample GMV portfolio is unbiased
-- statement:
--   Let $N \ge 2$ risky assets have returns that are i.i.d. over time and multivariate normal with mean $\mu$ and positive definite covariance $\Sigma$, let $\gamma > 0$, and let $h > N + 3$ be the length of the estimation window. From the $h$ returns form the maximum-likelihood estimators $\hat\mu_t$, $\hat\Sigma_t$, the sample GMV portfolio $\hat w_{g,t} = \hat\Sigma_t^{-1}1_N/(1_N'\hat\Sigma_t^{-1}1_N)$ and the sample zero-investment portfolio $\hat w_{z,t} = \hat\Sigma_t^{-1}(\hat\mu_t - 1_N\hat\mu_{g,t})$. Write $\sigma_g^2 = 1/(1_N'\Sigma^{-1}1_N)$, $\mu_g = 1_N'\Sigma^{-1}\mu\,\sigma_g^2$ and $\psi^2 = \mu'\Sigma^{-1}\mu - \mu_g^2/\sigma_g^2$. Then the out-of-sample mean $\mu_{g,t} = \hat w_{g,t}'\mu$ of the sample GMV portfolio is integrable and
--   $$E[\mu_{g,t}] = \mu_g.$$
--
--   It says that estimation error in the GMV portfolio does not bias its expected return; it supplies the constant term $\mu_g$ of Lemma 1.
--
--   **Formalization Note** $N \ge 2$, $\Sigma \succ 0$ and $\gamma > 0$ are implicit in the paper and made explicit. The statement asserts integrability as well as the value, because a Lean expectation of a non-integrable quantity is $0$. Lean's matrix inverse is $0$ on singular matrices; $\hat\Sigma_t$ is almost surely nonsingular here, so this does not matter.
-- source:
--   Kan, Wang & Zhou, Optimal portfolio choice with estimation risk: No risk-free asset case, submitted manuscript (version of November 2020; SSRN 2819254, TSpace), p. 32 (PDF 35), proof of Lemma 1, eq. (A9)

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_KanCombine_Optimal_Model

namespace KanCombine.Optimal

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

/-- (A9), p. 32: for h > N + 3, E[µ_{g,t}] = µ_g, where µ_{g,t} = ŵ_{g,t}′µ. -/
theorem eq_A9 {N h : ℕ} (M : Market N) (hM : KanStanding M h)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r) :
    Integrable (fun ω => muGt M (sampleData r ω)) P ∧
      ∫ ω, muGt M (sampleData r ω) ∂P = M.muG := by sorry

end KanCombine.Optimal
