-- Prove2me | Theorems.Thm_JHolomorphic_tsupport_normed_convolution_subset
-- name    : JHolomorphic.tsupport_normed_convolution_subset
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:01:37.8236+00:00
-- url     : https://prove2.me/theorems/384e8dc7-298b-45bb-a637-9ae261f89055
-- title:
--   The support of a normalized mollification lies in a thickening of the support
-- statement:
--   Let $g:\mathbb{C}\to\mathbb{R}$, let $\rho$ be a bump function centred at $0$ with outer radius $r$ and let $\rho_{\mathrm{n}}=\rho/\int\rho$. Then the closed support of $\rho_{\mathrm{n}}*g$ is contained in the closed $r$-thickening of the closed support of $g$.
--
--   **Formalization Note** For a bump function $\rho$ centred at $0$ (`ContDiffBump (0 : ℂ)`), $\rho_{\mathrm{n}}$ is `ρ.normed volume`, the multiple of $\rho$ with integral $1$; $\rho_{\mathrm{n}}*g$ is the convolution `ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g` with respect to Lebesgue measure on $\mathbb{C}$. The outer radius is `ρ.rOut`, closed supports are `tsupport`, and the closed thickening is `Metric.cthickening`.
-- source:
--   Standard (mollification).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

/-- The support of a mollification lies in the `rOut`-thickening of the support. -/
theorem tsupport_normed_convolution_subset (ρ : ContDiffBump (0 : ℂ)) (g : ℂ → ℝ) :
    tsupport (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) ⊆ cthickening ρ.rOut (tsupport g) := by
  sorry

end JHolomorphic
