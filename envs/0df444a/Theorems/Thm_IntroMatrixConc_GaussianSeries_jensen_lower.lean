-- Prove2me | Theorems.Thm_IntroMatrixConc_GaussianSeries_jensen_lower
-- name    : IntroMatrixConc.GaussianSeries.jensen_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:55.705254+00:00
-- url     : https://prove2.me/theorems/5693fe26-c527-4d0c-9c22-206f99e851b2
-- title:
--   §4.1.2, p. 44 — Jensen lower bound for a matrix Gaussian series
-- statement:
--   Let $Z=\sum_k\gamma_kB_k$ be a finite series of fixed complex $d_1\times d_2$ matrices with independent standard real Gaussian coefficients. Write $v(Z)=\max\{\|\mathbb E ZZ^*\|,\|\mathbb E Z^*Z\|\}$, with the Euclidean operator norm. Then
--
--   $$v(Z)\le \mathbb E\|Z\|^2.$$
--
--   This is the lower half of the second-moment comparison (4.1.7). The dimensions are positive, and the coefficient family may be empty.
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, §4.1.2, p. 44, Jensen display below (4.1.7)

import Mathlib
import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.GaussianSeries

/-- Tropp §4.1.2, p. 44: the Jensen lower bound in (4.1.7). -/
theorem jensen_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ N : ℕ} [NeZero d₁] [NeZero d₂]
    (B : Fin N → Matrix (Fin d₁) (Fin d₂) ℂ)
    (g : Fin N → Ω → ℝ)
    (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ)
    (hLaw : ∀ k, standardGaussianLaw μ (g k)) :
    let Z := fun ω => ∑ k, g k ω • B k
    rectSecondMoment μ Z ≤ ∫ ω, spectralNorm (Z ω) ^ 2 ∂μ := by sorry

end IntroMatrixConc.GaussianSeries
