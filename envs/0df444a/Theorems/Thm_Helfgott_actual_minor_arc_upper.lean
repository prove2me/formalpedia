-- Prove2me | Theorems.Thm_Helfgott_actual_minor_arc_upper
-- name    : Helfgott.actual_minor_arc_upper
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-04T23:46:15.735407+00:00
-- url     : https://prove2.me/theorems/306145b0-2c99-4d7f-a6b0-2dffb3587aeb
-- title:
--   Total minor-arc bound for the actual coordinated Goldbach smoothings
-- statement:
--   For every real x≥4.9×10²⁶, the complete integral over the complement of the major arcs M(8,150000,x) of |Sη+(x,α)|²|Sη*(x,α)| is at most 0.97392x²/49. The infinite exponential sums and the parity-dependent arcs are the published actual data definitions. This is the remaining substantive minor-arc theorem; its sharp compact-smoothing, large-sieve, smoothing and numerical estimates are not assumed proved.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equation (7.48), with the final κ=49 smoothing definitions. https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
open MeasureTheory

namespace Helfgott

theorem actual_minor_arc_upper (x : ℝ) (hx : (49 : ℝ)*10^25 ≤ x) :
    minorArcMass x ≤ (97392/100000 : ℝ)*(x^2/49) := by sorry

end Helfgott
