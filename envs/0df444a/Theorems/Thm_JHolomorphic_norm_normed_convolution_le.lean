-- Prove2me | Theorems.Thm_JHolomorphic_norm_normed_convolution_le
-- name    : JHolomorphic.norm_normed_convolution_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:59:58.129587+00:00
-- url     : https://prove2.me/theorems/7d2b1987-1e41-42bc-8431-6be4e17bbef0
-- title:
--   A normalized mollification of a function bounded by $M$ is bounded by $3M$
-- statement:
--   Let $g:\mathbb{C}\to\mathbb{R}$ be continuous with $|g|\le M$ everywhere, let $\rho$ be a bump function centred at $0$ and let $\rho_{\mathrm{n}}=\rho/\int\rho$. Then $|(\rho_{\mathrm{n}}*g)(z)|\le 3M$ for every $z\in\mathbb{C}$.
--
--   **Formalization Note** For a bump function $\rho$ centred at $0$ (`ContDiffBump (0 : ℂ)`), $\rho_{\mathrm{n}}$ is `ρ.normed volume`, the multiple of $\rho$ with integral $1$; $\rho_{\mathrm{n}}*g$ is the convolution `ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g` with respect to Lebesgue measure on $\mathbb{C}$.
-- source:
--   Standard (mollification).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

/-- A mollification of a bounded continuous function is bounded by three times the bound. -/
theorem norm_normed_convolution_le (ρ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (z : ℂ) :
    ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z‖ ≤ 3 * M := by
  sorry

end JHolomorphic
