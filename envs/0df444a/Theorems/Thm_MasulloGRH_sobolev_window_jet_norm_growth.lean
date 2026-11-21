-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_window_jet_norm_growth
-- name    : MasulloGRH.sobolev_window_jet_norm_growth
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:24:50.152188+00:00
-- url     : https://prove2.me/theorems/3e5fbf5c-08ef-49d5-92c8-598740aee1aa
-- title:
--   Windowed jet squared norms diverge with jet order
-- statement:
--   Fix a positive window half-width $\alpha>0$ and $s>1$. Then $$\int_{\mathbb R}e^{-2\alpha|x|}\frac{x^{2m}}{(1+x^2)^{s/2}}\,dx\longrightarrow+\infty\qquad(m\to\infty).$$ Each integral is finite. These are the squared weighted norms of the scalar logarithmic jets at the central real parameter $b=0$. Thus interior-window integrability for every order does not give a uniform upper bound over all orders.
--
--   This is an auxiliary check on the compact-parameter argument after the displayed norm on p. 447. It does not assert that zero multiplicities are unbounded, or that the actual zeta-indexed family contains jets of arbitrarily high order; it is not by itself a disproof of Proposition 10.2.2.2.
-- source:
--   Auxiliary consequence and scope check of the windowed norm in A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 447, proof of Proposition 10.2.2.2, together with the unrestricted interior jet-order formula (10.2.2.6) on p. 446. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The theorem concerns all scalar jet orders and is not claimed as a separately numbered assertion in the source.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem MasulloGRH.sobolev_window_jet_norm_growth (α s : ℝ) (hα : 0 < α) (hs : 1 < s) :
    Tendsto (fun m : ℕ => ∫ x : ℝ, Real.exp (-2 * α * |x|) *
      (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) atTop atTop := by sorry
