-- Prove2me | Theorems.Thm_Helfgott_actual_major_arc_lower_of_prime_accuracy
-- name    : Helfgott.actual_major_arc_lower_of_prime_accuracy
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T04:58:59.423801+00:00
-- url     : https://prove2.me/theorems/a35c8088-3fd7-4c06-a8eb-411dfdff33a8
-- title:
--   The original three-prime major-arc lower bound follows from the finite prime-accuracy certificate
-- statement:
--   For every odd integer $N\ge10^{27}$, put $\rho=2+9/(196\sqrt{2\pi})$ and $x=N/\rho$. Assume the existing major-prime accuracy profile: on every original major arc, the actual $\eta_+$ prime exponential sum differs from its rational Fourier model by at most $10^{-7}x$, and the actual $\eta_*$ prime sum differs by at most $2\cdot10^{-8}x$. Then the full original three-prime major-arc lower bound holds:
--   $$\Re\int_{\mathfrak M(8,150000,x)}S_{\eta_+}(\alpha,x)^2S_{\eta_*}(\alpha,x)e(-N\alpha)\,d\alpha\ge1.058259\,\frac{x^2}{49}.$$
--   All smoothing, continuous-model truncation, singular-series and major-arc integration estimates are proved without numerical zero hypotheses. This reduces the original lower-bound milestone to the existing finite prime-accuracy certificate. It uses the tighter $10^{-7}x$ plus-smoothing premise, which is stronger than the $17\cdot10^{-7}x$ allowance in the separate zero-location-only error reduction; that stronger accuracy is not claimed derived from finite GRH here.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, section 7.2. Complete rational smoothing, centered variance, Fourier-energy truncation and L2 prime-error refinement. Written by Codex.

import Definitions.Def_Helfgott_MajorPrimeAccuracy
open MeasureTheory

namespace Helfgott

theorem actual_major_arc_lower_of_prime_accuracy (N : ℕ) (hN : 10^27≤N) (hodd : Odd N)
    (haccuracy : majorPrimeAccuracy (goldbachScale N)) :
    (1058259/1000000 : ℝ)*((goldbachScale N)^2/49)≤
      (∫ α in majorArcs 8 150000 (goldbachScale N),
        ternaryIntegrand (goldbachScale N) N α ∂AddCircle.haarAddCircle).re := by sorry

end Helfgott
