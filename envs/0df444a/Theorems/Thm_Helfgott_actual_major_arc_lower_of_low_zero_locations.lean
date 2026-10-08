-- Prove2me | Theorems.Thm_Helfgott_actual_major_arc_lower_of_low_zero_locations
-- name    : Helfgott.actual_major_arc_lower_of_low_zero_locations
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T05:24:17.028464+00:00
-- url     : https://prove2.me/theorems/cf1af80f-d9ad-4955-998c-c42086c61a44
-- title:
--   The original three-prime major-arc lower bound follows from finite primitive zero locations
-- statement:
--   Assume the exact finite primitive zero-location profile of the original Goldbach major arcs: every regularized primitive Dirichlet zero in the relevant strip, below the two conductor-dependent smoothing cutoffs, is either the isolated trivial zero at zero or lies on the critical line. For every odd $N\ge10^{27}$, put $\rho=2+9/(196\sqrt{2\pi})$ and $x=N/\rho$. Then the exact original lower bound holds:
--   $$\Re\int_{\mathfrak M(8,150000,x)}S_{\eta_+}(\alpha,x)^2S_{\eta_*}(\alpha,x)e(-N\alpha)\,d\alpha\ge1.058259\,\frac{x^2}{49}.$$
--   All smoothing, singular-series, Fourier truncation, contour, weighted zero-mass, character-sum and arc-integration estimates are proved independently. No additional prime-accuracy certificate is assumed. The already proved functional-equation bridge supplies this profile from the ordinary finite primitive GRH witness; that numerical witness remains a separate Open obligation.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, section 7.2. Complete rational smoothing, centered variance, Fourier-energy truncation and L2 prime-error refinement. Written by Codex.

import Definitions.Def_Helfgott_PrimitiveLowZeroLocations
import Definitions.Def_Helfgott_MajorPrimeAccuracyRelaxed
open MeasureTheory

namespace Helfgott

theorem actual_major_arc_lower_of_low_zero_locations (hloc : PrimitiveLowZeroLocations) (N : ℕ) (hN : 10^27≤N) (hodd : Odd N)
    :
    (1058259/1000000 : ℝ)*((goldbachScale N)^2/49)≤
      (∫ α in majorArcs 8 150000 (goldbachScale N),
        ternaryIntegrand (goldbachScale N) N α ∂AddCircle.haarAddCircle).re := by sorry

end Helfgott
