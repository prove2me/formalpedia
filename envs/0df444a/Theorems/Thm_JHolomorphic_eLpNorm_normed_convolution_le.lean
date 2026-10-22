-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_normed_convolution_le
-- name    : JHolomorphic.eLpNorm_normed_convolution_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T17:29:51.334024+00:00
-- url     : https://prove2.me/theorems/f6822283-e71f-48f9-a0be-c135a1826219
-- title:
--   Mollification with a normed bump function does not increase $L^p$ norms on $\mathbb{C}$
-- statement:
--   Let $E$ be a real normed space, let $1\le p<\infty$, let $\rho$ be a smooth bump function on $\mathbb{C}$ centred at $0$, and let $\rho_1=\rho/\int\rho$ be its normalisation. For every almost everywhere strongly measurable $g:\mathbb{C}\to E$,
--
--   $$\|\rho_1*g\|_{L^p(\mathbb{C})}\le\|g\|_{L^p(\mathbb{C})},\qquad (\rho_1*g)(z)=\int_{\mathbb{C}}\rho_1(t)\,g(z-t)\,dt .$$
--
--   Both sides may be infinite. This gives uniform $L^p$ control of mollifications of vector-valued maps on the plane.
--
--   **Formalization Note** The bump function is a `ContDiffBump (0 : ℂ)` and its normalisation is `ρ.normed volume`. The convolution is Mathlib's `⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]`. $p$ is an `ENNReal` with `1 ≤ p` and `p ≠ ⊤`. $g$ is not assumed to lie in $L^p$, and $E$ is not assumed complete.
-- source:
--   Standard (elliptic regularity for the Cauchy–Riemann operator; weak derivatives and mollifiers).

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace JHolomorphic

open MeasureTheory Filter
open scoped Convolution ENNReal

/-- Mollification with a normed bump function does not increase `L^p` norms (`1 ≤ p < ∞`). -/
theorem eLpNorm_normed_convolution_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : ContDiffBump (0 : ℂ)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {g : ℂ → E}
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p volume ≤
      eLpNorm g p volume := by
  sorry

end JHolomorphic
