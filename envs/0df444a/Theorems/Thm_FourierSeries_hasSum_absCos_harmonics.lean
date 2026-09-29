-- Prove2me | Theorems.Thm_FourierSeries_hasSum_absCos_harmonics
-- name    : FourierSeries.hasSum_absCos_harmonics
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T11:14:56.184607+00:00
-- url     : https://prove2.me/theorems/8e736162-f2a6-48ee-947a-7612eb10c793
-- title:
--   The Fourier series of $|\cos\theta|$
-- statement:
--   **The Fourier expansion of the rectified cosine.**
--
--   The function $\theta \mapsto |\cos\theta|$ is even and $\pi$-periodic, so its Fourier series
--   contains only the cosines of even multiples of $\theta$. The expansion converges pointwise
--   everywhere to
--
--   $$|\cos\theta| \;=\; \frac{2}{\pi} \;+\; \frac{4}{\pi}\sum_{m=1}^{\infty}
--   \frac{(-1)^{m+1}\cos(2m\theta)}{4m^2-1}.$$
--
--   Equivalently, reindexing by $m \ge 0$, the series
--
--   $$\sum_{m=0}^{\infty} \frac{4}{\pi}\cdot
--   \frac{(-1)^{m}\cos\bigl(2(m+1)\theta\bigr)}{4(m+1)^2-1}$$
--
--   converges to $|\cos\theta| - \tfrac{2}{\pi}$.
--
--   The constant term $2/\pi$ is the mean value of $|\cos|$ over a period, and the coefficients
--   decay like $1/m^2$, which is why the series converges absolutely and uniformly — the
--   rectified cosine is continuous, with a corner rather than a jump at each zero of $\cos$.
--   The denominators $4m^2 - 1 = (2m-1)(2m+1)$ arise from
--   $\int_0^{\pi/2}\cos\theta\cos(2m\theta)\,d\theta$.
--
--   This expansion is the standard worked example of a Fourier series for a continuous but
--   non-smooth periodic function, and it appears as a technical tool wherever $|\cos|$ or
--   $|\sin|$ must be replaced by a trigonometric series — for instance in estimating mean values
--   of $|\zeta|$ along vertical lines, or in bounding absolute values of exponential sums.
--
--   **Formalization note.** The statement is given as a `HasSum` over $m : \mathbb{N}$, which
--   asserts unconditional convergence of the family to the stated value, rather than convergence
--   of a particular sequence of partial sums.
-- source:
--   Classical. Lean proof extracted from `Salt/MR/AbsCosFourier.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace FourierSeries

theorem hasSum_absCos_harmonics (θ : ℝ) :
    HasSum (fun m : ℕ => 4 / Real.pi
        * ((-1 : ℝ) ^ m * Real.cos (2 * ((m : ℝ) + 1) * θ) / (4 * ((m : ℝ) + 1) ^ 2 - 1)))
      (|Real.cos θ| - 2 / Real.pi) := by sorry

end FourierSeries
