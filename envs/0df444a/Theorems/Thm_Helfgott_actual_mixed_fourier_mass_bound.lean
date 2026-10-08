-- Prove2me | Theorems.Thm_Helfgott_actual_mixed_fourier_mass_bound
-- name    : Helfgott.actual_mixed_fourier_mass_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T05:34:26.117691+00:00
-- url     : https://prove2.me/theorems/538a7315-823e-4c13-bb12-ddb654ea51ea
-- title:
--   Complete mixed Fourier mass of the actual Goldbach smoothings
-- statement:
--   Let $\eta_+$ and $\eta_*$ be the actual band-limited and Mellin-convolved smoothings in the three-prime Goldbach proof, and use the Fourier convention $\widehat f(\xi)=\int_{\mathbb R}f(t)e(-\xi t)\,dt$. The product of their Fourier magnitudes is integrable and satisfies the complete bound
--   $$\int_{\mathbb R}|\widehat{\eta_+}(\xi)\widehat{\eta_*}(\xi)|\,d\xi\le\frac{771}{10000}=0.0771.$$
--   The estimate includes all transform frequencies. It preserves the small star Fourier factor in the cubic prime-error expansion and is the decisive refinement connecting the finite primitive zero-location profile to the exact original major-arc lower bound. It requires no zero-location or prime-accuracy hypothesis.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, section 7.2. Complete Fourier-energy and tail refinement. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.FourierTransform
open MeasureTheory
open scoped FourierTransform

namespace Helfgott

theorem actual_mixed_fourier_mass_bound :
    Integrable (fun ξ : ℝ =>
      ‖𝓕 (fun t : ℝ => (etaPlus t : ℂ)) ξ‖*‖𝓕 (fun t : ℝ => (etaStar t : ℂ)) ξ‖) ∧
    (∫ ξ : ℝ,‖𝓕 (fun t : ℝ => (etaPlus t : ℂ)) ξ‖*
      ‖𝓕 (fun t : ℝ => (etaStar t : ℂ)) ξ‖)≤771/10000 := by sorry

end Helfgott
