-- Prove2me | Theorems.Thm_IntroMatrixConc_Sampling_corollary_6_2_1
-- name    : IntroMatrixConc.Sampling.corollary_6_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:49.011608+00:00
-- url     : https://prove2.me/theorems/b69af92a-914a-4998-938b-c4f4445b391d
-- title:
--   Corollary 6.2.1 — matrix approximation by random sampling
-- statement:
--   Let $B$ be a fixed complex $d_1\times d_2$ matrix, where $d_1,d_2\ge1$. Let $R$ be a measurable random matrix of the same size with $\mathbb ER=B$ and $\|R\|\le L$ almost surely. Form $\overline R_n=n^{-1}\sum_{k=1}^{n}R_k$ from $n>0$ independent copies of $R$. Define
--
--   $$
--   m_2(R)=\max\{\|\mathbb E(RR^*)\|,\|\mathbb E(R^*R)\|\}.
--   $$
--
--   The estimator error has finite expected spectral norm, and
--
--   $$
--   \mathbb E\|\overline R_n-B\|\le
--   \sqrt{\frac{2m_2(R)\log(d_1+d_2)}{n}}+
--   \frac{2L\log(d_1+d_2)}{3n}.
--   $$
--
--   For every $t\ge0$, it also satisfies
--
--   $$
--   \mathbb P\{\|\overline R_n-B\|\ge t\}\le
--   (d_1+d_2)\exp\!\left(\frac{-nt^2/2}{m_2(R)+2Lt/3}\right).
--   $$
--
--   This gives both an expectation guarantee and a tail guarantee for empirical matrix approximation.
--
--   **Formalization Note** The almost-sure bound and measurability make the displayed expectations genuine Bochner integrals; the integrability of the error norm is also asserted explicitly. At a zero tail denominator, Lean's division convention makes the right side $d_1+d_2$, a valid but loose bound.
-- source:
--   Tropp, arXiv:1501.01571v1, Corollary 6.2.1, equations (6.2.4)–(6.2.6), p. 81 (PDF p. 87)

import Definitions.Def_IntroMatrixConc_Sampling_Defs
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.Sampling

/-- Tropp, Corollary 6.2.1, p. 81 (PDF p. 87), equations (6.2.5) and (6.2.6). -/
theorem corollary_6_2_1 {Ω : Type*} [MeasurableSpace Ω]
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
    Integrable (fun ω => spectralNorm (samplingEstimator R ω - B)) μ ∧
    (∫ ω, spectralNorm (samplingEstimator R ω - B) ∂μ) ≤
      Real.sqrt (2 * rectSecondMoment μ R₀ * Real.log (d₁ + d₂) / n) +
        2 * L * Real.log (d₁ + d₂) / (3 * n) ∧
    ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ spectralNorm (samplingEstimator R ω - B)}).toReal ≤
        (d₁ + d₂ : ℕ) * Real.exp
          ((-((n : ℝ) * t ^ 2) / 2) /
            (rectSecondMoment μ R₀ + 2 * L * t / 3)) := by sorry

end IntroMatrixConc.Sampling
