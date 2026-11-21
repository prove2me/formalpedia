-- Prove2me | Theorems.Thm_MasulloRH_finite_prime_tail_le_seven_over_three_halves_power
-- name    : MasulloRH.finite_prime_tail_le_seven_over_three_halves_power
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T04:38:53.804171+00:00
-- url     : https://prove2.me/theorems/a25cf66c-30a2-44ea-85da-fa7773c4026d
-- title:
--   Uniform finite prime tail bound without a logarithmic factor
-- statement:
--   Every finite segment of the reference prime tail past N≥196 has mass at most 7 divided by N to the three-halves power, independently of its upper endpoint.
-- source:
--   New telescoping dyadic estimate for the Masullo reference prime series.

import Mathlib
open ArithmeticFunction Finset

namespace MasulloRH
theorem finite_prime_tail_le_seven_over_three_halves_power (N K : ℕ) (hN : 196 ≤ N) :
    (∑ j ∈ Ioc N K,(vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤ 7/(N:ℝ)^(3/2:ℝ) := by sorry
end MasulloRH
