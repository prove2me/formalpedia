-- Prove2me | Theorems.Thm_IntroMatrixConc_GaussianSeries_eq_4_1_7
-- name    : IntroMatrixConc.GaussianSeries.eq_4_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:51.172286+00:00
-- url     : https://prove2.me/theorems/b354fada-cfc9-43e9-8117-b2c3c418976e
-- title:
--   (4.1.7), p. 43 — the squared norm of a matrix Gaussian series
-- statement:
--   Let $B_k$ be a finite family of fixed complex $d_1\times d_2$ matrices, where $d_1,d_2\ge1$, and let the $\gamma_k$ be independent standard real Gaussian variables. Set $Z=\sum_k\gamma_kB_k$ and $v(Z)=\max\{\|\mathbb E ZZ^*\|,\|\mathbb E Z^*Z\|\}$. Then $\|Z\|^2$ is integrable and
--
--   $$v(Z)\le\mathbb E\|Z\|^2\le 2v(Z)\bigl(1+\log(d_1+d_2)\bigr).$$
--
--   The result identifies the matrix variance as the scale of the squared operator norm, allowing the logarithmic dimension factor on the upper side.
--
--   **Formalization Note** Integrability is stated explicitly so that the Bochner integral cannot take Lean's default zero value for a nonintegrable function. An empty coefficient family is allowed and gives $Z=v(Z)=0$.
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, (4.1.7), pp. 43–44

import Mathlib
import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.GaussianSeries

/-- Tropp (4.1.7): both sides of the squared-norm comparison for a Gaussian series. -/
theorem eq_4_1_7 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ N : ℕ} [NeZero d₁] [NeZero d₂]
    (B : Fin N → Matrix (Fin d₁) (Fin d₂) ℂ)
    (g : Fin N → Ω → ℝ)
    (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ)
    (hLaw : ∀ k, standardGaussianLaw μ (g k)) :
    let Z := fun ω => ∑ k, g k ω • B k
    let v := rectSecondMoment μ Z
    Integrable (fun ω => spectralNorm (Z ω) ^ 2) μ ∧
      v ≤ ∫ ω, spectralNorm (Z ω) ^ 2 ∂μ ∧
      (∫ ω, spectralNorm (Z ω) ^ 2 ∂μ) ≤
        2 * v * (1 + Real.log (d₁ + d₂)) := by sorry

end IntroMatrixConc.GaussianSeries
