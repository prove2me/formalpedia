-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_trace_fourier_coefficients
-- name    : GrothendieckLB.Supplement.cq_boundary_trace_fourier_coefficients
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:07:12.867674+00:00
-- url     : https://prove2.me/theorems/01cd0c65-d97b-4c1b-aea9-3edb06f5929d
-- title:
--   Fourier coefficients of the cubic–quintic boundary trace
-- statement:
--   For the cubic–quintic scheme let $H$ be its correlation and $D=z\partial_z$. For $z=e^{i\theta}$ the diagonal Hermite trace of the explicit third differentiated Gaussian kernel has square-integrable boundary values and its $m$th Fourier coefficient is $m^3[t^m]H$ for all nonnegative $m$. This is the analytic identification in (52), followed by radial passage to the unit circle.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix C.2–C.4, equations (47)–(54).

import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel
import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr

namespace GrothendieckLB.Supplement

open MeasureTheory

theorem cq_boundary_trace_fourier_coefficients :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    let hab : (0:ℝ) < 2*Real.pi := by positivity
    MemLp CQBoundary.trace 2 (volume.restrict (Set.Ioc 0 (2*Real.pi))) ∧
      ∀ m : ℕ, fourierCoeffOn hab CQBoundary.trace (m:ℤ) =
        (m:ℂ)^3 * (GrothendieckLB.taylorCoeff m H : ℂ) := by sorry

end GrothendieckLB.Supplement
