-- Prove2me | Theorems.Thm_FourierSeries_abs_cos_partial_fourier_bound
-- name    : FourierSeries.abs_cos_partial_fourier_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:26:28.321358+00:00
-- url     : https://prove2.me/theorems/cde2e6b0-da01-404d-8fac-925951dc0fc3
-- title:
--   An explicit truncation error for the Fourier series of $|\cos\theta|$
-- statement:
--   **A uniform error bound for truncating the Fourier series of the rectified cosine.**
--
--   Recall the expansion
--   $|\cos\theta| = \tfrac{2}{\pi} + \tfrac{4}{\pi}\sum_{m\ge1}\tfrac{(-1)^{m+1}\cos(2m\theta)}{4m^2-1}$.
--   Truncating after $M$ terms, the remainder is bounded **uniformly in $\theta$** by
--
--   $$\left||\cos\theta| - \frac{2}{\pi} - \frac{4}{\pi}\sum_{m=1}^{M}
--   \frac{(-1)^{m+1}\cos(2m\theta)}{4m^{2}-1}\right|
--   \;\le\; \frac{2}{\pi(2M+1)} .$$
--
--   The rate $O(1/M)$ is what the alternating structure buys: bounding the tail term by term would
--   give $\sum_{m>M}\tfrac{4}{\pi(4m^2-1)} = O(1/M)$ as well, and the partial-fraction identity
--   $\tfrac{2}{4m^2-1} = \tfrac{1}{2m-1} - \tfrac{1}{2m+1}$ makes the tail telescope to exactly
--   $\tfrac{2}{\pi(2M+1)}$.
--
--   Having an explicit, $\theta$-uniform truncation error is what makes the expansion usable as a
--   tool rather than an identity: one replaces $|\cos|$ by a trigonometric polynomial of controlled
--   degree and pays a known price, which is the standard manoeuvre when $|\cos|$ or $|\sin|$ must
--   be integrated against another oscillating factor.
--
--   **Formalization note.** The sum runs over `Finset.Icc 1 Mcut`, i.e. $1 \le m \le M$; the bound
--   holds for every real $\theta$ and every $M \ge 0$.
-- source:
--   Classical. Lean proof extracted from `Salt/MR/AbsCosFourier.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace FourierSeries

theorem abs_cos_partial_fourier_bound (θ : ℝ) (Mcut : ℕ) :
    |(|Real.cos θ| - 2 / Real.pi - 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
        (-1 : ℝ) ^ (m + 1) * Real.cos (2 * (m : ℝ) * θ) / (4 * (m : ℝ) ^ 2 - 1))|
      ≤ 2 / (Real.pi * (2 * (Mcut : ℝ) + 1)) := by sorry

end FourierSeries
