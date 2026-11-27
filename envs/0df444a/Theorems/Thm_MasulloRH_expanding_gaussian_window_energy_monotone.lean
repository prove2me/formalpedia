-- Prove2me | Theorems.Thm_MasulloRH_expanding_gaussian_window_energy_monotone
-- name    : MasulloRH.expanding_gaussian_window_energy_monotone
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T22:25:45.618065+00:00
-- url     : https://prove2.me/theorems/59f021ec-3e94-4977-875c-a19da55fba8b
-- title:
--   Energy of a finite unit Gaussian residual increases with the expanding window
-- statement:
--   For any finite collection of real shifts and complex coefficients the weighted squared residual energy is nondecreasing along the full Gaussian windows.
-- source:
--   Masullo RH specialization, fixed unit Gaussian in the expanding weighted windows. The dyadic theta Mellin identity and the accepted finite-window energy identities are used at their registered types.

import Definitions.Def_MasulloRH_FixedGaussianTest

open MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

theorem MasulloRH.expanding_gaussian_window_energy_monotone {m : ℕ} (a : Fin m → ℂ) (y : Fin m → ℝ) {j k : ℕ} (h : j ≤ k) :
    energy (fullCenter j) (fullWidth j) (residual 0 a y) ≤ energy (fullCenter k) (fullWidth k) (residual 0 a y) := by sorry
