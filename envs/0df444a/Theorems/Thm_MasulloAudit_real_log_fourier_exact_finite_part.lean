-- Prove2me | Theorems.Thm_MasulloAudit_real_log_fourier_exact_finite_part
-- name    : MasulloAudit.real_log_fourier_exact_finite_part
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:11:41.223264+00:00
-- url     : https://prove2.me/theorems/4ea36fe0-594a-4db1-9a1a-9a75b47767a1
-- title:
--   Exact additive Fourier normalization of the real logarithmic finite part
-- statement:
--   Let $f$ be a complex Schwartz function on $\mathbb R$. Give the additive Fourier transform the phase $e^{-2\pi i x\xi}$ with Lebesgue measure, and write
--   $$T(f)=\int_{\mathbb R}\log|\xi|\,\widehat f(\xi)\,d\xi.$$
--   The real finite part exists, and it satisfies
--   $$
--   V(f)=\lim_{\delta\downarrow0}
--   \left(\int_{|x|\ge\delta}\frac{f(x)}{|x|}\,dx+2f(0)\log\delta\right),\qquad
--   T(f)=-\frac12 V(f)-\bigl(\gamma+\log(2\pi)\bigr) f(0),
--   $$
--   where $\gamma$ is the Euler–Mascheroni constant. In this self-dual additive normalization, the whole right-hand side of (B.4.3.13) in the 20 November 2026 draft is twice $T(f)$.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, pp. 618–620, Proposition B.4.3.2(1), Eq. (B.4.3.13) and Definition B.4.4.1, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Compare A. Connes, Trace Formula in Noncommutative Geometry and the Zeros of the Riemann Zeta Function, Appendix II, Eqs. (30) and (34), https://arxiv.org/pdf/math/9811068#page=74.

import Mathlib

open MeasureTheory

theorem MasulloAudit.real_log_fourier_exact_finite_part (f : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun δ : ℝ ↦ (∫ x in {x : ℝ | δ ≤ |x|}, f x / (|x| : ℝ)) +
        2 * f 0 * (Real.log δ : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-2 * ((∫ ξ : ℝ, (Real.log |ξ| : ℂ) * FourierTransform.fourier (f : ℝ → ℂ) ξ) +
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) : ℝ) * f 0))) := by sorry
