-- Prove2me | Theorems.Thm_MasulloRH_fixed_log_jet_mellin_decay_on_strip
-- name    : MasulloRH.fixed_log_jet_mellin_decay_on_strip
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:38:48.367801+00:00
-- url     : https://prove2.me/theorems/1fd9f16e-8bea-4333-bc1d-54f6ddae0587
-- title:
--   Rapid decay of each fixed logarithmic Mellin moment across a strip
-- statement:
--   For an admissible rational test φ, any closed vertical strip [a,b], any fixed logarithmic moment order d and any positive integer N, the integral of φ(exp y) y^d exp(sy) is bounded in absolute value by C |Im(s)|^(−N) at sufficiently large heights, uniformly across the strip. The constant and height threshold may depend on the order d. These moments supply the coefficients in the translated-jet expansion.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft, (10.4.2.29)–(10.4.2.34), p. 464, referring to the Mellin estimates (10.3.2.6)–(10.3.2.11), pp. 454–455. Fixed-order rational specialization using Proposition B.2.2.3.

import Definitions.Def_MasulloRH_RationalTrace
open MeasureTheory MasulloRH

theorem MasulloRH.fixed_log_jet_mellin_decay_on_strip (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (a b : ℝ) (hab : a < b) (d N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ |s.im| →
      ‖∫ y : ℝ, φ (Real.exp y) * (y:ℂ)^d * Complex.exp (s*y)‖ ≤ C/|s.im|^N := by sorry
