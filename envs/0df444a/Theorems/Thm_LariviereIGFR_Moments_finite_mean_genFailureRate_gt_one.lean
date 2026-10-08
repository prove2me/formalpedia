-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_finite_mean_genFailureRate_gt_one
-- name    : LariviereIGFR.Moments.finite_mean_genFailureRate_gt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:06.600974+00:00
-- url     : https://prove2.me/theorems/8443883f-a719-4c59-87ce-208ff7cd940e
-- title:
--   p. 603, after Theorem 2 — an IGFR law with support (α, ∞) and a finite mean has g(ξ) > 1 eventually
-- statement:
--   Let $X\ge 0$ have regular density $\phi$, support $(\alpha,\infty)$ with $\alpha\ge 0$, and be IGFR, with generalized failure rate $g(\xi)=\xi h(\xi)$. If $\mathbb E[X]<\infty$, then there is a finite $y$ with
--   $$
--   g(\xi)>1\qquad\text{for all }\xi>y .
--   $$
--
--   In the pricing problem of the paper's introduction a finite optimal price exists when the generalized failure rate exceeds one at a finite point; this result says a finite mean of the reservation-value distribution suffices.
--
--   **Formalization Note** The page's "it is sufficient to assume that the distribution of reservation values has a finite mean" is stated in the setting of Theorem 2 (IGFR, support $(\alpha,\infty)$); the conclusion is the paper's "the generalized failure rate exceeds one at a finite point", in the form that holds for all points beyond it. The mean is `nthMoment μ 1`, valued in $[0,\infty]$.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3, paragraph after Theorem 2

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- p. 603, after Theorem 2: if `X` is IGFR with support `(α, ∞)` and has a finite mean, then the
generalized failure rate exceeds one at every point beyond some finite `y`. -/
theorem finite_mean_genFailureRate_gt_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : LariviereIGFR.Char.IsRegDensity μ φ)
    (α : ℝ) (hsupp : HasSupportIoi μ α) (higfr : LariviereIGFR.Char.IsIGFR μ φ)
    (hmean : nthMoment μ 1 < ⊤) :
    ∃ y : ℝ, ∀ ξ, y < ξ → 1 < LariviereIGFR.Char.genFailureRate μ φ ξ := by sorry

end LariviereIGFR.Moments
