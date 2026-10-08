-- Prove2me | Theorems.Thm_Helfgott_actual_major_arc_lower
-- name    : Helfgott.actual_major_arc_lower
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-04T23:45:48.806225+00:00
-- url     : https://prove2.me/theorems/d67a4358-2f4f-42f3-b7f1-1883a87d563e
-- title:
--   Total major-arc lower bound at the actual Goldbach scale
-- statement:
--   For odd N≥10²⁷, at x=N/(2+9/(196√(2π))), the real part of the major-arc integral of the actual ternary Fourier integrand is at least 1.058259x²/49. The arcs include the paper’s separate odd/even denominator ranges and widths. This is the remaining substantive major-arc bound; its singular series, band-limited smoothing approximation, explicit L-function errors and verified numerical inputs remain to be proved.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (3.5), (7.14) and (7.25). The real-part formulation expresses the lower bound on the complex integral. https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
open MeasureTheory

namespace Helfgott

theorem actual_major_arc_lower (N : ℕ) (hN : 10^27 ≤ N) (hodd : Odd N) :
    (1058259/1000000 : ℝ)*((goldbachScale N)^2/49) ≤
      (∫ α in majorArcs 8 150000 (goldbachScale N),
        ternaryIntegrand (goldbachScale N) N α ∂AddCircle.haarAddCircle).re := by sorry

end Helfgott
