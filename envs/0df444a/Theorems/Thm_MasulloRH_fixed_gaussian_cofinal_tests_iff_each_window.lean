-- Prove2me | Theorems.Thm_MasulloRH_fixed_gaussian_cofinal_tests_iff_each_window
-- name    : MasulloRH.fixed_gaussian_cofinal_tests_iff_each_window
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T19:23:36.82796+00:00
-- url     : https://prove2.me/theorems/10ebdd86-d035-4f28-a23d-3f2baaf868fb
-- title:
--   One sequence of increasing accuracy suffices for all fixed-Gaussian windows
-- statement:
--   Arbitrary accuracy on every expanding window is equivalent to finding, for each positive integer j, a rational finite approximation of squared error less than 1/(j+1) on some window with index k at least j+1.
-- source:
--   Developed for the Masullo theta-window argument and the centered Möbius target. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_MasulloRH_FixedGaussianTest

open MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation MeasureTheory

theorem MasulloRH.fixed_gaussian_cofinal_tests_iff_each_window : (∀ k : ℕ, FullApprox k) ↔
    ∀ j : ℕ, 0<j → ∃ k : ℕ, j+1≤k ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy (fullCenter k) (fullWidth k) (residual 0
        (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) < 1/((j:ℝ)+1) := by sorry
