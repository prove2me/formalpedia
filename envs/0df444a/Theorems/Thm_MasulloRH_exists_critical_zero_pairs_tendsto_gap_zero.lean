-- Prove2me | Theorems.Thm_MasulloRH_exists_critical_zero_pairs_tendsto_gap_zero
-- name    : MasulloRH.exists_critical_zero_pairs_tendsto_gap_zero
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:41:30.696975+00:00
-- url     : https://prove2.me/theorems/6bc4810d-2627-46b1-a6c1-f48b1fd0928f
-- title:
--   Distinct critical-line zeta zeros with gaps tending to zero
-- statement:
--   There are sequences of positive real ordinates $a_n,b_n$ with $a_n\ne b_n$ for all $n$, such that
--   $$\zeta(\tfrac12+ia_n)=\zeta(\tfrac12+ib_n)=0,\qquad a_n-b_n\longrightarrow 0.$$
--
--   This follows from the cumulative Riemann–von Mangoldt formula and a positive lower proportion of distinct critical-line zeros. A count growing faster than linearly in the height forces two distinct ordinates into one of the intervals of any prescribed fixed width. Such pairs are the arithmetic input to the norm estimate for the zero-order spectral vectors used in the rational case of Masullo’s equation (10.3.1.18).
-- source:
--   Conrey, More than two fifths of the zeros of the Riemann zeta function are on the critical line, J. Reine Angew. Math. 399 (1989), pp. 1–26, https://doi.org/10.1515/crll.1989.399.1. The proof can use the stronger formal Zeta23 theorem thmA0_cumulative. Application to Masullo, The Music of the Primes, 20 November 2026 draft, pp. 443–444 and 451, equations (10.2.1.11) and (10.3.1.18), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf.

import Mathlib

open Filter
open scoped Topology

theorem MasulloRH.exists_critical_zero_pairs_tendsto_gap_zero :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n ∧ 0 < b n ∧ a n ≠ b n ∧
        riemannZeta ((1 / 2 : ℂ) + (a n : ℂ) * Complex.I) = 0 ∧
        riemannZeta ((1 / 2 : ℂ) + (b n : ℂ) * Complex.I) = 0) ∧
      Tendsto (fun n ↦ a n - b n) atTop (𝓝 0) := by sorry
