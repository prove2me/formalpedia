-- Prove2me | Theorems.Thm_GaussianMellinBound_large_delta
-- name    : GaussianMellinBound.large_delta
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-24T00:13:33.531685+00:00
-- url     : https://prove2.me/theorems/2a2475fa-de97-4841-9351-0693c60afcd1
-- title:
--   Uniform modulus comparison for the Gaussian Mellin transform $F_\delta$ on $-23/16 \le t \le -1$ for $|\delta| \ge 1$
-- statement:
--   Let $e(x) = e^{2\pi i x}$ denote the standard additive character, and for each real frequency parameter $\delta \in \mathbb{R}$ let
--
--   $$
--   F_\delta(s) := \int_0^\infty u^{s - 1} e^{-u^2 / 2} e(\delta u) \, du
--   $$
--
--   be the Mellin transform of the twisted Gaussian smoothing weight $u \mapsto e^{-u^2 / 2} e(\delta u)$ for $\operatorname{Re}(s) > 0$. If $|\delta| \ge 1$ and $t \in \mathbb{R}$ satisfies $-\frac{23}{16} \le t \le -1$, then
--
--   $$
--   \left|F_\delta\!\left(\tfrac{1}{2} + i t\right)\right| \le \frac{3}{2} \left|F_\delta\!\left(\tfrac{1}{2} - i\right)\right|.
--   $$
--
--   In Helfgott's explicit-formula treatment of major-arc exponential sums over primes, sums of $|F_\delta(\rho)|$ over low-lying zeros $\rho = \frac{1}{2} + i t$ of Dirichlet $L$-functions in short horizontal bands below $t = -1$ are bounded in terms of the single reference value $|F_\delta(\frac{1}{2} - i)|$. This theorem establishes the uniform comparison with constant $\frac{3}{2}$ throughout the ordinate band $-\frac{23}{16} \le t \le -1$ in the oscillatory regime $|\delta| \ge 1$.
--
--   **Formalization Note** The transform $F_\delta(s)$ is expressed directly via Mathlib's `mellin` operator applied to `fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ))`.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, https://arxiv.org/abs/1305.2897, Section 4.1 (page 17) and Section 6.3 (displays 4.42--4.43, page 43)

import Mathlib
open Real

namespace GaussianMellinBound
theorem large_delta (δ : ℝ) (hδ : 1 ≤ |δ|) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
        ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end GaussianMellinBound
