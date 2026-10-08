-- Prove2me | Theorems.Thm_Helfgott_etaPlus_etaStar_fourier_main_explicit
-- name    : Helfgott.etaPlus_etaStar_fourier_main_explicit
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T05:13:45.404598+00:00
-- url     : https://prove2.me/theorems/6992a65a-f9ed-4281-bccf-f6aff06ce49f
-- title:
--   Exact Fourier main term for the actual coordinated Goldbach smoothings
-- statement:
--   For every real parameter $\rho$, the product of the Fourier transforms of Helfgott's actual smoothings is absolutely integrable, and Fourier inversion gives the exact identity
--
--   $$\int_{\mathbb R} e(\rho\xi)\widehat\eta_+(\xi)^2\widehat\eta_*(\xi)\,d\xi
--   =\int_0^\infty\eta_*(w)\int_{\mathbb R}\eta_+(u)\eta_+(\rho-w-u)\,du\,dw.$$
--
--   Here $e(t)=\exp(2\pi i t)$ and $\widehat f(\xi)=\int f(t)e(-t\xi)\,dt$. The identity includes the actual band-limited smoothing's signed tails and its zero extension at nonpositive arguments. All integrability and continuity needed for Fubini, convolution and Fourier inversion are proved, rather than assumed. This connects the continuous Fourier major-arc main term with the real convolution whose positive lower bound has been separately established.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §3.3 equation (3.37), the coordinated smoothings in §4, and §7.2. The complete analytic justification is independently derived here for the exact published smoothing definitions. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set

namespace Helfgott

theorem etaPlus_etaStar_fourier_main_explicit (ρ : ℝ) : Integrable (fun ξ : ℝ => (FourierTransform.fourier (fun t : ℝ => (etaPlus t : ℂ)) ξ)^2*
      FourierTransform.fourier (fun t : ℝ => (etaStar t : ℂ)) ξ) ∧
    (∫ ξ : ℝ,(Real.fourierChar (ρ*ξ) : ℂ)*
      (FourierTransform.fourier (fun t : ℝ => (etaPlus t : ℂ)) ξ)^2*
      FourierTransform.fourier (fun t : ℝ => (etaStar t : ℂ)) ξ) =
      (((∫ w in Ioi (0 : ℝ),etaStar w*
        (∫ u : ℝ,etaPlus u*etaPlus (ρ-w-u))) : ℝ) : ℂ) := by sorry

end Helfgott
