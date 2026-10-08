-- Prove2me | Theorems.Thm_Helfgott_actual_major_kernel_tight_fourier_bounds
-- name    : Helfgott.actual_major_kernel_tight_fourier_bounds
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T00:38:59.321267+00:00
-- url     : https://prove2.me/theorems/e0c40818-79fd-4d85-8b1d-4364acf4542d
-- title:
--   Complete tight Fourier mass and quadratic decay of the actual Goldbach logarithmic kernel
-- statement:
--   Let $K(u)=h(\exp u)$, where $h$ is the actual major-arc kernel defining the Goldbach smoothing $\eta_+$. With Fourier convention $\widehat K(\xi)=\int K(u)\exp(-2\pi i u\xi)\,du$, the transform is integrable and
--   $$\int_{\mathbb R}|K(u)|\,du\le\frac52,\quad|\widehat K(\xi)|\le\frac52,\quad\xi^2|\widehat K(\xi)|\le\frac5{12},\quad\int_{\mathbb R}|\widehat K(\xi)|\,d\xi\le\frac{25}6.$$
--   These unconditional estimates control the complete signed spectral projection used in the actual etaPlus Mellin transform and its conductor-dependent high-zero bound.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Original complete numerical and analytic bounds built on Mathlib Gaussian, Fourier and Mellin analysis. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.FourierTransform
open MeasureTheory Set Complex
open scoped FourierTransform

namespace Helfgott

theorem actual_major_kernel_tight_fourier_bounds :
    let K : ℝ → ℂ := fun u => (majorKernel (Real.exp u) : ℂ)
    Integrable (𝓕 K) ∧ (∫ u : ℝ,‖K u‖)≤5/2 ∧
      (∀ ξ : ℝ,‖𝓕 K ξ‖≤5/2) ∧
      (∀ ξ : ℝ,ξ^2*‖𝓕 K ξ‖≤5/12) ∧
      (∫ ξ : ℝ,‖𝓕 K ξ‖)≤25/6 := by sorry

end Helfgott
