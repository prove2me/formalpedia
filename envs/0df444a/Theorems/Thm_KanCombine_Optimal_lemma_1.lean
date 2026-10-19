-- Prove2me | Theorems.Thm_KanCombine_Optimal_lemma_1
-- name    : KanCombine.Optimal.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:08.979538+00:00
-- url     : https://prove2.me/theorems/d3d53857-c0b0-4cda-afff-4d5317d4fd5a
-- title:
--   Lemma 1, p. 8 — for h > N + 3 and constant c̃, E[U(ŵ_t(c̃))] is the quadratic (17) in c̃
-- statement:
--   Let $N \ge 2$ risky assets have returns that are i.i.d. over time and multivariate normal with mean $\mu$ and positive definite covariance $\Sigma$, let $\gamma > 0$, and let $h > N + 3$ be the length of the estimation window. From the $h$ returns form the maximum-likelihood estimators $\hat\mu_t$, $\hat\Sigma_t$, the sample GMV portfolio $\hat w_{g,t} = \hat\Sigma_t^{-1}1_N/(1_N'\hat\Sigma_t^{-1}1_N)$ and the sample zero-investment portfolio $\hat w_{z,t} = \hat\Sigma_t^{-1}(\hat\mu_t - 1_N\hat\mu_{g,t})$. Write $\sigma_g^2 = 1/(1_N'\Sigma^{-1}1_N)$, $\mu_g = 1_N'\Sigma^{-1}\mu\,\sigma_g^2$ and $\psi^2 = \mu'\Sigma^{-1}\mu - \mu_g^2/\sigma_g^2$. For a constant scalar $\tilde c$ consider the combining portfolio $\hat w_t(\tilde c) = \hat w_{g,t} + \tilde c\,\hat w_{z,t}/\gamma$ and its out-of-sample utility $U(\hat w_t(\tilde c)) = \hat w_t(\tilde c)'\mu - \frac{\gamma}{2}\hat w_t(\tilde c)'\Sigma\hat w_t(\tilde c)$, a random variable through the sample. Then for every $\tilde c \in \mathbb R$, $U(\hat w_t(\tilde c))$ is integrable and
--   $$E[U(\hat w_t(\tilde c))] = \mu_g - \frac{\gamma(h-2)\sigma_g^2}{2(h-N-1)} + \frac{h}{\gamma(h-N-1)}\left[\tilde c\psi^2 - \frac{\tilde c^2(h-2)(h\psi^2+N-1)}{2(h-N)(h-N-3)}\right].$$
--
--   The first two terms are the expected out-of-sample utility of the sample GMV portfolio; the bracket is the contribution of the exposure $\tilde c\,\hat w_{z,t}/\gamma$, which depends on the market only through $\psi^2$. The formula is the basis of the optimal combining coefficient of §2.3.
--
--   **Formalization Note** $N \ge 2$, $\Sigma \succ 0$ and $\gamma > 0$ are implicit in the paper and made explicit. The statement asserts integrability as well as the value, because a Lean expectation of a non-integrable quantity is $0$. Lean's matrix inverse is $0$ on singular matrices; $\hat\Sigma_t$ is almost surely nonsingular here, so this does not matter.
-- source:
--   Kan, Wang & Zhou, Optimal portfolio choice with estimation risk: No risk-free asset case, submitted manuscript (version of November 2020; SSRN 2819254, TSpace), p. 8 (PDF 11), Lemma 1, eq. (17); proof pp. 31–32 (PDF 34–35)

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_KanCombine_Optimal_Model

namespace KanCombine.Optimal

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

/-- Lemma 1, p. 8, eq. (17): for h > N + 3 and every constant c̃, the expected out-of-sample utility of ŵ_t(c̃) = ŵ_{g,t} + c̃ŵ_{z,t}/γ exists and equals (17). -/
theorem lemma_1 {N h : ℕ} (M : Market N) (hM : KanStanding M h)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r) :
    ∀ c : ℝ, Integrable (fun ω => M.U (wComb M c (sampleData r ω))) P ∧
      expUtility M P r c =
        M.muG - M.gamma * ((h : ℝ) - 2) * M.sigmaG2 / (2 * ((h : ℝ) - N - 1)) +
          (h : ℝ) / (M.gamma * ((h : ℝ) - N - 1)) *
            (c * M.psi2 - c ^ 2 * ((h : ℝ) - 2) * ((h : ℝ) * M.psi2 + N - 1) /
              (2 * ((h : ℝ) - N) * ((h : ℝ) - N - 3))) := by sorry

end KanCombine.Optimal
