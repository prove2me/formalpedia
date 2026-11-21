-- Prove2me | Theorems.Thm_NymanBeurling_damped_spectral_vanishing_of_ratio_bound
-- name    : NymanBeurling.damped_spectral_vanishing_of_ratio_bound
-- status  : Proved
-- author  : @pragyan
-- created : 2026-11-21T04:04:50.411923+00:00
-- url     : https://prove2.me/theorems/bd929771-31ef-49f1-b24d-fe9d5138c77e
-- title:
--   Vanishing spectral residual energy from a uniform shifted-zeta ratio bound
-- statement:
--   Assume the uniform critical-line shifted-zeta ratio bound. For every $\delta>0$, sufficiently small positive $\varepsilon$ then satisfy
--   $$\int_{\mathbb R}|F_\varepsilon(t)|^2\,dt<\delta,$$
--   and the integrand is integrable. Here
--   $$F_\varepsilon(t)=\frac{1-\zeta(s)(\zeta(s+\varepsilon)^{-1}-\zeta(1+\varepsilon)^{-1})}{s},\qquad s=1/2-it.$$
--   This conditional analytic implication is an open formalization obligation, distinct from the open ratio-bound hypothesis. At nonzero boundary values of zeta the spectral residual tends to zero; the discrete exceptional zero set is null. The ratio hypothesis, unconditional zeta growth, and the pole at one supply the domination and scalar limiting ingredients. No Nyman--Beurling residual estimate or RH theorem is assumed.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/pdf/math/0607733 . Theorem 2 proof pp.140–141, second dominated-convergence step. The paper derives the ratio bound from RH; the present implication instead takes only the explicit ratio bound as a hypothesis. The exceptional critical-line zeros require an almost-everywhere formulation of pointwise convergence, rather than an everywhere assertion.

import Definitions.Def_NymanBeurling_DampedMellinFrontiers
import Definitions.Def_NymanBeurling_DampedResidualLimits
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

theorem NymanBeurling.damped_spectral_vanishing_of_ratio_bound
    (hratio : NymanBeurling.ShiftedZetaRatioBound) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1/2 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Integrable (fun t : ℝ => ‖NymanBeurling.dampedSpectralResidual ε t‖^2) ∧
      (∫ t : ℝ, ‖NymanBeurling.dampedSpectralResidual ε t‖^2) < δ := by sorry
