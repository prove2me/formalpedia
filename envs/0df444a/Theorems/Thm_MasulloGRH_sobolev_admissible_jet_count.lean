-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_admissible_jet_count
-- name    : MasulloGRH.sobolev_admissible_jet_count
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:26:47.745221+00:00
-- url     : https://prove2.me/theorems/abf8f3d8-85e3-423c-9488-2256c7a731ba
-- title:
--   The admissible scalar Sobolev jet count uses a ceiling
-- statement:
--   Let $N$ be a natural number and $s>1$ a real number. Among the jet orders $0\le m<N$, the number for which the squared scalar Sobolev weight is Lebesgue integrable is
--
--   $$\#\left\{m\in\mathbb N:m<N,\ \frac{x^{2m}}{(1+x^2)^{s/2}}\in L^1(\mathbb R)\right\}=\min\left\{N,\left\lceil\frac{s-1}{2}\right\rceil\right\}.$$
--
--   The strict integrability threshold is the one in Proposition 9.1.2.5, equation (9.1.2.16), p. 402, of the frozen Masullo draft. This counting corollary keeps the endpoint excluded. At $s=3$ and $N=2$ the count is $1$, whereas the floor-plus-one expression printed in (10.2.1.6) and (10.3.1.4) evaluates to $2$.
--
--   This is a count of scalar integrable weights. It does not assert the existence of a zero of multiplicity $N$, nor identify a spectral quotient or prove its trace formula. The corrected count is stated separately from the printed formula.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf: arithmetic consequence of the strict threshold (9.1.2.16) in Proposition 9.1.2.5, p. 402. Comparison with the printed counts (10.2.1.6), p. 440, and (10.3.1.4), p. 448; this is the corrected scalar integrability count, not a transcription of those counts.

import Theorems.Thm_MasulloGRH_sobolev_jet_weight_integrable_iff
import Mathlib.Order.Interval.Set.Nat
set_option autoImplicit false
open MeasureTheory Set

theorem MasulloGRH.sobolev_admissible_jet_count (N : ℕ) (s : ℝ) (hs : 1 < s) :
    {m : ℕ | m < N ∧ Integrable (fun x : ℝ =>
      x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))}.ncard =
      min N (Nat.ceil ((s - 1) / 2)) := by sorry
