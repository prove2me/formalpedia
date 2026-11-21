-- Prove2me | Theorems.Thm_MasulloRH_lift_mellin_jet_matrix_entry
-- name    : MasulloRH.lift_mellin_jet_matrix_entry
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:37:20.856631+00:00
-- url     : https://prove2.me/theorems/c2a3f59e-395e-4a2d-8a95-b6471819d216
-- title:
--   Mellin matrix entry of convolution on a biorthogonal lift
-- statement:
--   Let the logarithmic lift density G have the prescribed biorthogonal moments through degree m at the spectral parameter s. Pairing its convolution against the degree-m jet gives zero for j>m. For j≤m the result is the binomial coefficient times the logarithmic Mellin moment of the test of order m−j. Absolute integrability of the finitely many moments of the lift is assumed.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft of 20 November 2026, Theorem 10.4.2.8, (10.4.2.29)–(10.4.2.33), p. 464, and the computation in (10.3.1.8)–(10.3.1.14) recalled by Theorem 10.3.2.1.

import Mathlib

open MeasureTheory

theorem MasulloRH.lift_mellin_jet_matrix_entry (φ G : ℝ → ℂ) (s : ℂ) (m j : ℕ)
    (hi : ∀ d ≤ m, Integrable (fun x : ℝ => G x * (x:ℂ)^d * Complex.exp (s*x)))
    (hb : ∀ d ≤ m, (∫ x : ℝ, G x * (x:ℂ)^d * Complex.exp (s*x)) =
      if d = j then 1 else 0) :
    (∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ,
      G x * ((x:ℂ)+y)^m * Complex.exp (s*((x:ℂ)+y))) =
      if j ≤ m then (m.choose j : ℂ) * ∫ y : ℝ,
        φ (Real.exp y) * (y:ℂ)^(m-j) * Complex.exp (s*y) else 0 := by sorry
