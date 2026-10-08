-- Prove2me | Theorems.Thm_Helfgott_actual_kernel_fourth_polynomial_moment_bound
-- name    : Helfgott.actual_kernel_fourth_polynomial_moment_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T11:04:25.997273+00:00
-- url     : https://prove2.me/theorems/7effa56e-468b-471c-89a5-8a2734e9db27
-- title:
--   Certified fourth-derivative polynomial moment for the actual Goldbach smoothing kernel
-- statement:
--   The integral from 0 to 2 of abs(t*(128-452*t-124*t^2+537*t^3+27*t^4-97*t^5-20*t^6-t^7))*exp(t-1/2) is at most 1730. The polynomial is the exact fourth logarithmic derivative density of the actual Helfgott major smoothing kernel. This numerical moment controls the fourth-order Fourier tail and the sharp etaPlus coefficient error.
-- source:
--   Exact rational Bernstein certificates on 32 mesh intervals, proved by polynomial identities and nonnegativity; an elementary rational exponential bound; interval integration and addition. Supporting input for the actual smoothing of H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2. Written by Codex.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory

namespace Helfgott

theorem actual_kernel_fourth_polynomial_moment_bound :
    (∫ t in (0 : ℝ)..2,|t*((128 : ℝ)-452*t-124*t^2+537*t^3+27*t^4-97*t^5-20*t^6-t^7)| *Real.exp (t-1/2)) ≤ 1730 := by sorry

end Helfgott
