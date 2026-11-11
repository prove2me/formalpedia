-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_zero_mass_bound
-- name    : OrderSelProphet.Kernel.zero_mass_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:59:46.35016+00:00
-- url     : https://prove2.me/theorems/2b79a599-0d95-4729-85ec-8c7c71813303
-- title:
--   Appendix F.6.1, eq. (128) — the zero mass vector: $\bar\ell_\lambda\le\Gamma_1+\Gamma_1^2e^{-b_4}/(1-\Gamma_1)<0.749<U_{\rm cert}$
-- statement:
--   Fix $\lambda\in\Lambda$ with mass vector $x(\lambda)=0$. Then $\lambda(u_r)=0$ for almost every $r\in[0,b_4]$, the area curve $A_\lambda$ vanishes on $[0,1-e^{-b_4}]$, $Y(0)\ge1-e^{-b_4}$, and
--   $$\bar\ell_\lambda\le\Gamma_1Y(0)+\frac{\Gamma_1}{1-\Gamma_1}(1-Y(0))\le\Gamma_1+\frac{\Gamma_1^2e^{-b_4}}{1-\Gamma_1}<\Gamma_1+\frac{\Gamma_1^2}{600(1-\Gamma_1)}<0.749<U_{\rm cert}.\quad(128)$$
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: x_max = 0 → massVec λ g = 0 for every g; reason: the coordinates are nonnegative, so x_max = 0 iff all vanish
--   - encoding: ℓ̄_λ ≤ … (real) → auxLoad λ ≤ ENNReal.ofReal(…); reason: the auxiliary load is in ℝ≥0∞
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Appendix F.6.1, eq. (128), p. 56

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Certificate

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Appendix F.6.1, eq. (128), p. 56: the bound for the zero mass vector. -/
theorem zero_mass_bound (lam : Profile) (h0 : ∀ g, massVec lam.1 g = 0) :
    (∀ᵐ r ∂(volume.restrict (Icc 0 (blockEnd 4))), lam.1 (uA r) = 0) ∧
      (∀ x ∈ Icc 0 (1 - Real.exp (-blockEnd 4)), areaP lam.1 x = 0) ∧
      1 - Real.exp (-blockEnd 4) ≤ Yc lam.1 0 ∧
      auxLoad lam.1 ≤ ENNReal.ofReal
        (Gamma1 * Yc lam.1 0 + Gamma1 / (1 - Gamma1) * (1 - Yc lam.1 0)) ∧
      Gamma1 * Yc lam.1 0 + Gamma1 / (1 - Gamma1) * (1 - Yc lam.1 0) ≤
        Gamma1 + Gamma1 ^ 2 * Real.exp (-blockEnd 4) / (1 - Gamma1) ∧
      Gamma1 + Gamma1 ^ 2 * Real.exp (-blockEnd 4) / (1 - Gamma1) <
        Gamma1 + Gamma1 ^ 2 / (600 * (1 - Gamma1)) ∧
      Gamma1 + Gamma1 ^ 2 / (600 * (1 - Gamma1)) < 0.749 ∧
      (0.749 : ℝ) < Ucert := by sorry

end OrderSelProphet.Kernel
