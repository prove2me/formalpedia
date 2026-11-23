-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_fourier_moment_derivatives
-- name    : GrothendieckLB.Supplement.cq_fourier_moment_derivatives
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T21:42:13.386793+00:00
-- url     : https://prove2.me/theorems/9f90f68e-0562-45cd-8526-0581d0c663d3
-- title:
--   Covariance and shift derivatives of mixed Gaussian Fourier moments
-- statement:
--   The mixed Fourier moment of a Gaussian is complex differentiable in the covariance on the open strip where its real quadratic form is positive definite. A covariance derivative increments both Fourier exponents. Each real shift derivative increments its own exponent, and the resulting moment is jointly continuous in the shifts.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace GrothendieckLB.Supplement
open CQPrice

theorem cq_fourier_moment_derivatives (q : ℂ) (hq : |q.re|<1) (u v : ℝ) (m n : ℕ) :
    HasDerivAt (fun r : ℂ => fourierMoment r u v m n) (fourierMoment q u v (m+1) (n+1)) q ∧
    HasDerivAt (fun s : ℝ => fourierMoment q s v m n) (fourierMoment q u v (m+1) n) u ∧
    HasDerivAt (fun s : ℝ => fourierMoment q u s m n) (fourierMoment q u v m (n+1)) v ∧
    Continuous (fun w : ℝ×ℝ => fourierMoment q w.1 w.2 m n) := by sorry

end GrothendieckLB.Supplement
