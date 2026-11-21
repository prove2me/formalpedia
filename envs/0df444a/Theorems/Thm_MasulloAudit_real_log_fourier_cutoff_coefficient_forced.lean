-- Prove2me | Theorems.Thm_MasulloAudit_real_log_fourier_cutoff_coefficient_forced
-- name    : MasulloAudit.real_log_fourier_cutoff_coefficient_forced
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:50:18.912224+00:00
-- url     : https://prove2.me/theorems/daadacac-e9bc-4cfc-96e3-aa47b50f3b35
-- title:
--   Additive Fourier scaling forces a half in the real cutoff formula
-- statement:
--   For a compactly supported smooth real test $f$, let $V(f)$ be the finite part with the counterterm printed in (B.4.3.13):
--   $$
--   V(f)=\lim_{\delta\downarrow0}
--   \left(\int_{|x|\ge\delta}\frac{f(x)}{|x|}\,dx+2f(0)\log\delta\right).
--   $$
--   Use the usual additive Fourier transform $\widehat f(\xi)=\int f(x)e^{-2\pi i x\xi}\,dx$ and self-dual Lebesgue measure. If real constants $c,k$ satisfy
--   $$
--   \int_{\mathbb R}\log|\xi|\,\widehat f(\xi)\,d\xi=-cV(f)-kf(0)
--   $$
--   for every such test, then $c=1/2$. In particular, the coefficient $c=1$ in the printed cutoff evaluation is incompatible with the additive Fourier definition. The theorem determines the multiplier by dilation, independently of the pole constant $k$.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, pp. 618–620, Proposition B.4.3.2(1), Eq. (B.4.3.13) and Definition B.4.4.1. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Compare A. Connes, Trace Formula in Noncommutative Geometry and the Zeros of the Riemann Zeta Function, Appendix II, Eqs. (30) and (34), https://arxiv.org/pdf/math/9811068#page=74.

import Mathlib

open MeasureTheory Filter FourierTransform
open scoped Topology SchwartzMap FourierTransform

theorem MasulloAudit.real_log_fourier_cutoff_coefficient_forced (c k : ℝ)
    (h : ∀ f : 𝓢(ℝ, ℝ), HasCompactSupport f → ∀ v : ℝ,
      Tendsto (fun δ : ℝ ↦ (∫ x in {x : ℝ | δ ≤ |x|}, f x / |x|) +
        2*f 0*Real.log δ) (𝓝[>] (0 : ℝ)) (𝓝 v) →
      (∫ ξ : ℝ, (Real.log |ξ| : ℂ) * 𝓕 (fun x : ℝ ↦ (f x : ℂ)) ξ) =
        ((-c*v-k*f 0 : ℝ) : ℂ)) :
    c = 1 / 2 := by sorry
