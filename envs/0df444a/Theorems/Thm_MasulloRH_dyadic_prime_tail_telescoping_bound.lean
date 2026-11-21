-- Prove2me | Theorems.Thm_MasulloRH_dyadic_prime_tail_telescoping_bound
-- name    : MasulloRH.dyadic_prime_tail_telescoping_bound
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T04:37:33.162268+00:00
-- url     : https://prove2.me/theorems/8b4458f9-4bf0-4593-b9ef-09bed6076df2
-- title:
--   Telescoping upper bound for dyadic blocks of the reference prime series
-- statement:
--   For each integer X at least 196 the prime-series contribution between X and 2X is bounded by the difference of the explicit envelopes 7/X^(3/2) and 7/(2X)^(3/2).
-- source:
--   New application of the elementary Chebyshev upper estimate to Masullo reference prime sums.

import Mathlib
open ArithmeticFunction Finset

namespace MasulloRH
theorem dyadic_prime_tail_telescoping_bound (X : ℕ) (hX : 196 ≤ X) :
    (∑ j ∈ Ioc X (2*X), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
      7/(X:ℝ)^(3/2:ℝ) - 7/(2*(X:ℝ))^(3/2:ℝ) := by sorry
end MasulloRH
