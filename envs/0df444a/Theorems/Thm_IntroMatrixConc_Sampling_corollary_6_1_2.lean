-- Prove2me | Theorems.Thm_IntroMatrixConc_Sampling_corollary_6_1_2
-- name    : IntroMatrixConc.Sampling.corollary_6_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:01.257717+00:00
-- url     : https://prove2.me/theorems/5d136b61-8a22-4cca-8cc0-fd15a66f3426
-- title:
--   Corollary 6.1.2 — matrix Bernstein for uncentered summands
-- statement:
--   Let $S_1,\ldots,S_N$ be independent measurable complex $d_1\times d_2$ random matrices on a probability space, with $d_1,d_2\ge1$. Suppose each has a finite expectation and its deviation satisfies $\|S_k-\mathbb E S_k\|\le L$ almost surely, where $L\ge0$. Set $Z=\sum_kS_k$ and
--
--   $$
--   v(Z)=\max\{\|\mathbb E[(Z-\mathbb EZ)(Z-\mathbb EZ)^*]\|,\|\mathbb E[(Z-\mathbb EZ)^*(Z-\mathbb EZ)]\|\}.
--   $$
--
--   Then $v(Z)$ also equals the maximum of the norms of the corresponding sums of centered second moments. Moreover,
--
--   $$
--   \mathbb E\|Z-\mathbb EZ\|\le\sqrt{2v(Z)\log(d_1+d_2)}+\frac{L\log(d_1+d_2)}{3},
--   $$
--
--   and, for every $t\ge0$,
--
--   $$
--   \mathbb P\{\|Z-\mathbb EZ\|\ge t\}\le(d_1+d_2)\exp\!\left(-\frac{t^2/2}{v(Z)+Lt/3}\right).
--   $$
--
--   This version applies matrix Bernstein directly to summands that need not have zero mean.
--
--   **Formalization Note** Finite expectations are explicit integrability hypotheses, following the book's regularity convention in §2.2.1. At a zero denominator, the displayed exponential uses Lean's total division convention; the resulting bound is harmless because the centered sum is then zero almost surely.
-- source:
--   Tropp, arXiv:1501.01571v1, Corollary 6.1.2, p. 77 (PDF p. 83)

import Definitions.Def_IntroMatrixConc_Sampling_Defs

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.Sampling

/-- Tropp, Corollary 6.1.2, p. 77 (PDF p. 83). -/
theorem corollary_6_1_2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ N : ℕ} [NeZero d₁] [NeZero d₂]
    (S : Fin N → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (S k))
    (hInt : ∀ k, Integrable (S k) μ)
    (hIndep : iIndepFun S μ)
    (hBound : ∀ k, ∀ᵐ ω ∂μ,
      spectralNorm (S k ω - ∫ ω, S k ω ∂μ) ≤ L) :
    let Z := fun ω => ∑ k, S k ω
    let V := rectSecondMoment μ (fun ω => Z ω - ∫ ω, Z ω ∂μ)
    V = max
      (spectralNorm (∑ k, ∫ ω,
        (S k ω - ∫ η, S k η ∂μ) * (S k ω - ∫ η, S k η ∂μ).conjTranspose ∂μ))
      (spectralNorm (∑ k, ∫ ω,
        (S k ω - ∫ η, S k η ∂μ).conjTranspose * (S k ω - ∫ η, S k η ∂μ) ∂μ)) ∧
    (∫ ω, spectralNorm (Z ω - ∫ η, Z η ∂μ) ∂μ) ≤
      Real.sqrt (2 * V * Real.log (d₁ + d₂)) + L * Real.log (d₁ + d₂) / 3 ∧
    ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ spectralNorm (Z ω - ∫ η, Z η ∂μ)}).toReal ≤
        (d₁ + d₂ : ℕ) * Real.exp (-(t ^ 2 / 2) / (V + L * t / 3)) := by sorry

end IntroMatrixConc.Sampling
