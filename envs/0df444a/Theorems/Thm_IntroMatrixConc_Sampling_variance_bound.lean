-- Prove2me | Theorems.Thm_IntroMatrixConc_Sampling_variance_bound
-- name    : IntroMatrixConc.Sampling.variance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:34.904993+00:00
-- url     : https://prove2.me/theorems/924f27e1-b35c-4f5e-afba-1af6a2ee887a
-- title:
--   Proof of Corollary 6.2.1 — estimator variance bound
-- statement:
--   Let $R_1,\ldots,R_n$ be independent copies of a measurable complex $d_1\times d_2$ random matrix $R$, with $n>0$ and $d_1,d_2\ge1$. Suppose $\mathbb ER=B$ and $\|R\|\le L$ almost surely. Write $\overline R_n=n^{-1}\sum_kR_k$ and $m_2(R)=\max\{\|\mathbb E RR^*\|,\|\mathbb E R^*R\|\}$. Then
--
--   $$
--   v(\overline R_n-B)\le\frac{m_2(R)}{n},
--   $$
--
--   where $v$ is the rectangular second-moment statistic of the centered estimator error. This bounds the variance parameter in the matrix Bernstein estimate by one sample's second moment.
--
--   **Formalization Note** The almost-sure spectral norm bound ensures that all matrix-valued second moments are integrable.
-- source:
--   Tropp, arXiv:1501.01571v1, §6.2.2, proof of Corollary 6.2.1, p. 82 (PDF p. 88), 'In summary' display

import Definitions.Def_IntroMatrixConc_Sampling_Defs
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.Sampling

/-- Tropp, proof of Corollary 6.2.1, p. 82 (PDF p. 88): `v(Z) ≤ m₂(R)/n`. -/
theorem variance_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ n : ℕ} [NeZero d₁] [NeZero d₂]
    (R₀ : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (R : Fin n → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (B : Matrix (Fin d₁) (Fin d₂) ℂ) (L : ℝ)
    (hn : 0 < n)
    (hMeas₀ : Measurable R₀) (hMeas : ∀ k, Measurable (R k))
    (hIndep : iIndepFun R μ)
    (hCopies : ∀ k, IdentDistrib (R k) R₀ μ μ)
    (hMean : (∫ ω, R₀ ω ∂μ) = B)
    (hBound : ∀ᵐ ω ∂μ, spectralNorm (R₀ ω) ≤ L) :
    rectSecondMoment μ (fun ω => samplingEstimator R ω - B) ≤
      rectSecondMoment μ R₀ / n := by sorry

end IntroMatrixConc.Sampling
