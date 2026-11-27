-- Prove2me | Theorems.Thm_MasulloRH_window_energy_sandwiched_by_endpoint_mellin_errors
-- name    : MasulloRH.window_energy_sandwiched_by_endpoint_mellin_errors
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T04:02:32.15185+00:00
-- url     : https://prove2.me/theorems/31c65389-1d99-58e1-a507-920c959ad6ee
-- title:
--   Gaussian window energy bounded above and below by its two endpoint Mellin errors
-- statement:
--   For each rational approximant and each 0<c<1, its squared vertical Mellin error equals 2π times its zero-width energy. For any window contained in the open strip, 2π times its energy lies between the maximum and the sum of the two endpoint errors. All the displayed integrands are integrable.
-- source:
--   For the fixed Gaussian approximation on the expanding windows in the Masullo specialization. https://prove2.me/theorems/a73312ae-c4b7-4b9d-8ac1-61f52cc8523d The exact Laplace transform and the Mellin–Plancherel normalization are the published statements. https://prove2.me/theorems/ad7d0d3b-eb45-4b3b-88e7-470916794553 and https://prove2.me/theorems/ac289eb0-066f-51e2-97c4-4fa14b311435

import Definitions.Def_MasulloRH_VerticalThetaApproximation

open MeasureTheory MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation

theorem MasulloRH.window_energy_sandwiched_by_endpoint_mellin_errors {m : ℕ} (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) :
    (∀ c : ℝ, 0 < c → c < 1 → Integrable (fun t : ℝ => ‖spectrum c a y t‖^2) ∧
      mass c a y = 2*Real.pi*energy c 0 (approximation a y)) ∧
    (∀ c b : ℝ, 0 ≤ b → 0 < c-b → c+b < 1 →
      Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖approximation a y x‖^2) ∧
      max (mass (c-b) a y) (mass (c+b) a y) ≤ 2*Real.pi*energy c b (approximation a y) ∧
      2*Real.pi*energy c b (approximation a y) ≤ mass (c-b) a y + mass (c+b) a y) := by sorry
