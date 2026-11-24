-- Prove2me | Theorems.Thm_GaussianMellinBound_small_delta_p1
-- name    : GaussianMellinBound.small_delta_p1
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-24T03:33:00.103708+00:00
-- url     : https://prove2.me/theorems/361e1fb5-6c97-4513-b669-a0be67eb05e4
-- title:
--   Uniform modulus comparison for the Gaussian Mellin transform $F_\delta$ on $-23/16 \le t \le -1$ for $-1 \le \delta \le -3/4$
-- statement:
--   Let $e(x) = e^{2\pi i x}$ denote the standard additive character, and for each real frequency parameter $\delta \in \mathbb{R}$ let
--
--   $$
--   F_\delta(s) := \int_0^\infty u^{s - 1} e^{-u^2 / 2} e(\delta u) \, du
--   $$
--
--   be the Mellin transform of the twisted Gaussian smoothing weight $u \mapsto e^{-u^2 / 2} e(\delta u)$ for $\operatorname{Re}(s) > 0$. If $-1 \le \delta \le -\frac{3}{4}$ and $t \in \mathbb{R}$ satisfies $-\frac{23}{16} \le t \le -1$, then
--
--   $$
--   \left|F_\delta\!\left(\tfrac{1}{2} + i t\right)\right| \le \frac{3}{2} \left|F_\delta\!\left(\tfrac{1}{2} - i\right)\right|.
--   $$
--
--   In Helfgott's explicit-formula bounds for major-arc exponential sums over primes, low-lying zeros $\rho = \frac{1}{2} + i t$ in horizontal strips below $t = -1$ are controlled by comparing $|F_\delta(\frac{1}{2} + i t)|$ against $|F_\delta(\frac{1}{2} - i)|$. This theorem establishes the uniform factor-$\frac{3}{2}$ comparison across the frequency sub-interval $-1 \le \delta \le -\frac{3}{4}$.
--
--   **Formalization Note** The transform $F_\delta(s)$ is expressed via Mathlib's `mellin` operator applied to `fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ))`.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, https://arxiv.org/abs/1305.2897, Section 4.1 (page 17) and Section 6.3 (displays 4.42--4.43, page 43)

import Mathlib
open Real

namespace GaussianMellinBound
theorem small_delta_p1 (δ : ℝ) (hd_lo : -1 ≤ δ) (hd_hi : δ ≤ -(3 / 4)) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
        ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end GaussianMellinBound
