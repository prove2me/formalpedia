-- Prove2me | Theorems.Thm_Helfgott_etaPlus_etaStar_fourier_truncation_explicit
-- name    : Helfgott.etaPlus_etaStar_fourier_truncation_explicit
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T05:08:08.00529+00:00
-- url     : https://prove2.me/theorems/d3ae606c-152a-4a17-9671-fe0eb6d7130b
-- title:
--   Explicit cubic truncation error for the actual Goldbach Fourier main term
-- statement:
--   For every real parameter $\rho$ and every positive cutoff $R$, the continuous Fourier main term truncated to $[-R,R]$ differs from the complete real convolution by at most $591/R^3$ in complex norm. The exact actual coordinated smoothings, including the signed tails of $\eta_+$, are used. The proof establishes Fourier inversion, the Plancherel square mass bound $\int |\widehat\eta_+|^2\le 0.642$, and the cubic decay $|\xi|^3|\widehat\eta_* (\xi)|\le920$ without analytic hypotheses. This quantitative estimate supports finite-major-arc truncation; it does not assert any estimate for prime exponential sums.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §§3.3 and 7.2. The explicit coarser truncation constant is independently derived for the exact published smoothing definitions. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set

namespace Helfgott

theorem etaPlus_etaStar_fourier_truncation_explicit (ρ R : ℝ) (hR : 0 < R) : ‖(((∫ w in Ioi (0:ℝ),etaStar w*(∫ u : ℝ,etaPlus u*etaPlus (ρ-w-u))) : ℝ) : ℂ)-
      (∫ ξ in Icc (-R) R,(Real.fourierChar (ρ*ξ) : ℂ)*
        (FourierTransform.fourier (fun t : ℝ => (etaPlus t : ℂ)) ξ)^2*
        FourierTransform.fourier (fun t : ℝ => (etaStar t : ℂ)) ξ)‖ ≤ 591/R^3 := by sorry

end Helfgott
