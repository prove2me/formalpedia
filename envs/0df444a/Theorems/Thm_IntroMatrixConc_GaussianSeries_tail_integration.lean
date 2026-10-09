-- Prove2me | Theorems.Thm_IntroMatrixConc_GaussianSeries_tail_integration
-- name    : IntroMatrixConc.GaussianSeries.tail_integration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:48.991988+00:00
-- url     : https://prove2.me/theorems/cb733b0f-7e2c-43a9-a26b-39c2d88b7803
-- title:
--   §4.1.2, p. 44 — tail integration at a positive split point
-- statement:
--   Let $Z$ be a measurable complex $d_1\times d_2$ random matrix on a probability space, with positive variance statistic $v(Z)=\max\{\|\mathbb E ZZ^*\|,\|\mathbb E Z^*Z\|\}$. Suppose that for every $t\ge0$,
--
--   $$\mathbb P\{\|Z\|\ge t\}\le(d_1+d_2)\exp\!\left(-\frac{t^2}{2v(Z)}\right).$$
--
--   For every split point $a>0$, the squared norm is integrable and
--
--   $$\mathbb E\|Z\|^2\le a^2+2v(Z)(d_1+d_2)\exp\!\left(-\frac{a^2}{2v(Z)}\right).$$
--
--   This is the quantitative tail-integration step used for the upper half of (4.1.7).
--
--   **Formalization Note** The page applies the step to a Gaussian series. The statement isolates the step for any measurable matrix satisfying exactly its stated tail bound; positive variance makes the displayed denominator meaningful.
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, §4.1.2, p. 44, tail-integration display below (4.1.7)

import Mathlib
import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.GaussianSeries

/-- Tropp §4.1.2, p. 44: integrate the displayed tail bound at a split point. -/
theorem tail_integration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    (Z : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (hMeas : Measurable Z)
    (hv : 0 < rectSecondMoment μ Z)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
        (d₁ + d₂ : ℕ) * Real.exp (-(t ^ 2) / (2 * rectSecondMoment μ Z)))
    (a : ℝ) (ha : 0 < a) :
    Integrable (fun ω => spectralNorm (Z ω) ^ 2) μ ∧
      (∫ ω, spectralNorm (Z ω) ^ 2 ∂μ) ≤
        a ^ 2 + 2 * rectSecondMoment μ Z * (d₁ + d₂ : ℕ) *
          Real.exp (-(a ^ 2) / (2 * rectSecondMoment μ Z)) := by sorry

end IntroMatrixConc.GaussianSeries
