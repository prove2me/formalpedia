-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_window_boundary_blowup
-- name    : MasulloGRH.sobolev_window_boundary_blowup
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:27:00.698173+00:00
-- url     : https://prove2.me/theorems/49bd47fe-1608-42e7-b71f-2ce823a45d8f
-- title:
--   Excluded jet orders diverge as the window boundary is approached
-- statement:
--   Let $m\in\mathbb N$, $\alpha\ge0$, and $1<s\le2m+1$. For any real sequence $b_n\to\alpha$, the nonnegative integrals satisfy $$\int_{\mathbb R}e^{2b_nx-2\alpha|x|}\frac{x^{2m}}{(1+x^2)^{s/2}}\,dx\longrightarrow+\infty.$$ The integral here is interpreted in the extended nonnegative reals. If $\alpha>0$ and every $b_n$ lies strictly inside $(-\alpha,\alpha)$, the previously proved windowed integrability criterion ensures that each integral is finite, although these values are unbounded.
--
--   This describes the failure of a uniform scalar norm bound when an excluded boundary jet order approaches the edge from the interior. It is a scope check for the compactness argument on p. 447, not a claim that a zeta-zero sequence has these parameters or a disproof of the source proposition for its spectral family.
-- source:
--   Auxiliary consequence of the windowed norm in A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 447, proof of Proposition 10.2.2.2, and the interior/boundary distinction in equations (10.2.2.5)–(10.2.2.6), p. 446. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This limit statement is not a separately numbered source assertion; it supplies a precise boundary analysis of the displayed scalar norm.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem MasulloGRH.sobolev_window_boundary_blowup (m : ℕ) (s α : ℝ) (hs : 1 < s) (hα : 0 ≤ α)
    (horder : s ≤ 2 * (m : ℝ) + 1) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 α)) :
    Tendsto (fun n => ∫⁻ x : ℝ, ENNReal.ofReal
      (Real.exp (2 * b n * x - 2 * α * |x|) *
        (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)))) atTop (𝓝 ⊤) := by sorry
