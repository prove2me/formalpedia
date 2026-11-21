-- Prove2me | Theorems.Thm_MasulloAudit_real_log_fourier_eq_neg_half_integral_of_zero_at_zero
-- name    : MasulloAudit.real_log_fourier_eq_neg_half_integral_of_zero_at_zero
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:00:56.982182+00:00
-- url     : https://prove2.me/theorems/345df13f-e68a-4467-8553-f7ac12cedadc
-- title:
--   The real logarithmic Fourier pairing on Schwartz tests vanishing at zero
-- statement:
--   Let $f$ be a complex Schwartz function on $\mathbb R$ with $f(0)=0$. For the self-dual additive Fourier transform
--   $$\widehat f(\xi)=\int_{\mathbb R}f(x)e^{-2\pi i x\xi}\,dx,$$
--   one has
--   $$\int_{\mathbb R}\log|\xi|\,\widehat f(\xi)\,d\xi
--   =-\frac12\int_{\mathbb R}\frac{f(x)}{|x|}\,dx.$$
--   Both integrals are absolutely convergent. This is the real local logarithmic Fourier pairing from (B.4.4.1) evaluated on tests for which the additive pole term vanishes.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, pp. 618–620, Eq. (B.4.3.13) and Definition B.4.4.1, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Compare A. Connes, Trace Formula in Noncommutative Geometry and the Zeros of the Riemann Zeta Function, Appendix II, Eqs. (30) and (34), https://arxiv.org/pdf/math/9811068#page=74.

import Mathlib

open MeasureTheory

theorem MasulloAudit.real_log_fourier_eq_neg_half_integral_of_zero_at_zero (f : SchwartzMap ℝ ℂ) (hf : f 0 = 0) :
    (∫ ξ : ℝ, (Real.log |ξ| : ℂ) * FourierTransform.fourier (f : ℝ → ℂ) ξ) =
      -(2 : ℂ)⁻¹ * ∫ x : ℝ, f x / (|x| : ℝ) := by sorry
