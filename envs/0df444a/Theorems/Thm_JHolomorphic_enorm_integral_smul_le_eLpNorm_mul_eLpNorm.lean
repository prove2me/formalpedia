-- Prove2me | Theorems.Thm_JHolomorphic_enorm_integral_smul_le_eLpNorm_mul_eLpNorm
-- name    : JHolomorphic.enorm_integral_smul_le_eLpNorm_mul_eLpNorm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T09:25:10.900985+00:00
-- url     : https://prove2.me/theorems/6bca0b2c-fc33-4d39-8427-55f62d89963f
-- title:
--   Hölder's inequality for a scalar-weighted Bochner integral
-- statement:
--   Let $(\alpha,\mu)$ be a measure space, $1<p<\infty$ and $q=p/(p-1)$. For every a.e. strongly measurable real function $\varphi$ and every a.e. strongly measurable map $f$ into a real normed space,
--   $$\Big\|\int\varphi\,f\,d\mu\Big\|\le\|\varphi\|_{L^q(\mu)}\,\|f\|_{L^p(\mu)}$$
--   in $[0,\infty]$, where the Bochner integral of a non-integrable map is $0$.
--
--   **Formalization Note** Stated with extended norms: `‖∫ x, φ x • f x ∂μ‖ₑ ≤ eLpNorm φ (ENNReal.ofReal (p / (p - 1))) μ * eLpNorm f (ENNReal.ofReal p) μ`.
-- source:
--   Hölder's inequality (standard)

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace JHolomorphic

open MeasureTheory
open scoped ENNReal

/-- Hölder's inequality for a scalar-weighted Bochner integral: for `1 < p < ∞`, a real function
`φ` and a map `f` into a real normed space, `‖∫ φ • f dμ‖ ≤ ‖φ‖_{L^{p/(p-1)}(μ)} ‖f‖_{L^p(μ)}`. -/
theorem enorm_integral_smul_le_eLpNorm_mul_eLpNorm {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} (p : ℝ) (hp : 1 < p) {φ : α → ℝ}
    {f : α → E} (hφ : AEStronglyMeasurable φ μ) (hf : AEStronglyMeasurable f μ) :
    ‖∫ x, φ x • f x ∂μ‖ₑ ≤
      eLpNorm φ (ENNReal.ofReal (p / (p - 1))) μ * eLpNorm f (ENNReal.ofReal p) μ := by
  sorry

end JHolomorphic
