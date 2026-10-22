-- Prove2me | Theorems.Thm_JHolomorphic_fderiv_normed_convolution_apply
-- name    : JHolomorphic.fderiv_normed_convolution_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:06:36.560747+00:00
-- url     : https://prove2.me/theorems/2920d341-99b8-411c-8f67-d2b8a12326fb
-- title:
--   Directional derivatives commute with mollification of $C^1$ functions on $\mathbb{C}$
-- statement:
--   Let $\varphi:\mathbb{C}\to\mathbb{R}$ be $C^1$ with compact support, let $\rho$ be a bump function centred at $0$ and let $\rho_{\mathrm{n}}=\rho/\int\rho$ be its normalization. Then for all $z,v\in\mathbb{C}$, $D(\rho_{\mathrm{n}}*\varphi)(z)\,v=\big(\rho_{\mathrm{n}}*(D\varphi(\cdot)\,v)\big)(z)$.
--
--   **Formalization Note** For a bump function $\rho$ centred at $0$ (`ContDiffBump (0 : ℂ)`), $\rho_{\mathrm{n}}$ is `ρ.normed volume`, the multiple of $\rho$ with integral $1$; $\rho_{\mathrm{n}}*g$ is the convolution `ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g` with respect to Lebesgue measure on $\mathbb{C}$. The derivatives are `fderiv ℝ`.
-- source:
--   Standard (mollification).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

/-- Directional derivatives of a mollified `C¹` function are mollified directional derivatives. -/
theorem fderiv_normed_convolution_apply (ρ : ContDiffBump (0 : ℂ)) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (z v : ℂ) :
    fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] φ) z v =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun x => fderiv ℝ φ x v) z := by
  sorry

end JHolomorphic
