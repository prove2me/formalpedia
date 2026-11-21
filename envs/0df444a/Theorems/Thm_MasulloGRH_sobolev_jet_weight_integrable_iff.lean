-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_jet_weight_integrable_iff
-- name    : MasulloGRH.sobolev_jet_weight_integrable_iff
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:25:18.971175+00:00
-- url     : https://prove2.me/theorems/1dd3fabf-7e26-47d2-a880-9c0d4deb474b
-- title:
--   Sobolev jet weight integrability has a strict threshold
-- statement:
--   For an integer $m\ge0$ and a real number $s>1$, the one-dimensional squared jet weight satisfies
--
--   $$\frac{x^{2m}}{(1+x^2)^{s/2}}\in L^1(\mathbb R,dx)\quad\Longleftrightarrow\quad 2m+1<s.$$
--
--   Equivalently, the admissible jet orders obey the strict inequality $m<(s-1)/2$. In particular, the first-order weight at $s=3$ is not integrable.
--
--   This is the real-variable integrability calculation in the proof of Proposition 9.1.2.5, p. 402, of the frozen Masullo draft. After logarithmic norm coordinates and removal of the unitary phase, it is the analytic part of the Sobolev membership test. The statement is about the real Lebesgue integral; it does not formalize the Haar-measure reduction, the spectral quotient, or the existence of a multiple zero. It provides a precise check on the endpoint convention in (10.2.1.6) and (10.3.1.4), which print a floor-plus-one count.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Proposition 9.1.2.5, p. 402, equation (9.1.2.16) and the final integral in its proof; compare (10.2.1.6), p. 440 and (10.3.1.4), p. 448. Real-variable specialization of the integrability calculation.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem MasulloGRH.sobolev_jet_weight_integrable_iff (m : ℕ) (s : ℝ) (hs : 1 < s) :
    Integrable (fun x : ℝ => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)) ↔
      (2 * (m : ℝ) + 1 < s) := by sorry
