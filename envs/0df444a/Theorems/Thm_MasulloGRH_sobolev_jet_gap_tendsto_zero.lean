-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_jet_gap_tendsto_zero
-- name    : MasulloGRH.sobolev_jet_gap_tendsto_zero
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:18:33.822507+00:00
-- url     : https://prove2.me/theorems/44deff80-4585-492c-b1b1-cd8a5eb66e3c
-- title:
--   Nearby frequencies give nearby weighted Sobolev jets
-- statement:
--   Let $m\in\mathbb N$ and $s>2m+1$. If real sequences $a_n,b_n$ satisfy $a_n-b_n\to0$, then $$\int_{\mathbb R}|e^{ia_nx}-e^{ib_nx}|^2\frac{x^{2m}}{(1+x^2)^{s/2}}\,dx\longrightarrow0.$$ Thus the weighted $L^2$ distance between the logarithmic jets with these frequencies tends to zero, even when the frequencies themselves are unbounded. Under $t=e^x$, this is the positive-real Haar version for $t^{ia_n}(\log t)^m$ and $t^{ib_n}(\log t)^m$. This auxiliary result supplies the analytic closeness input in discussions of the biorthogonal bounds in Chapter 10. It makes no assertion about the distribution of zeta zeros or the abstract spectral quotient.
-- source:
--   Auxiliary consequence of the scalar weighted norm in A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 447, proof of Proposition 10.2.2.2, specialized to the zero window and positive-real logarithmic coordinates, and p. 402, Proposition 9.1.2.5. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This continuity lemma is not stated there as a separately numbered theorem; it supports the mission discussion on nearby frequencies and biorthogonal norms.

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

theorem MasulloGRH.sobolev_jet_gap_tendsto_zero (m : ℕ) (s : ℝ)
    (hs : 2 * (m : ℝ) + 1 < s) (a b : ℕ → ℝ)
    (hab : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : ℝ,
      ‖Complex.exp (((a n * x : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((b n * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 *
      (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) atTop (𝓝 0) := by sorry
