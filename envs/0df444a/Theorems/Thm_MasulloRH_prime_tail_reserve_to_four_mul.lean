-- Prove2me | Theorems.Thm_MasulloRH_prime_tail_reserve_to_four_mul
-- name    : MasulloRH.prime_tail_reserve_to_four_mul
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:20:14.248459+00:00
-- url     : https://prove2.me/theorems/d1d57b6a-6092-49dc-812a-a1832069ee71
-- title:
--   A weighted prime-tail reserve between N and 4N
-- statement:
--   For each integer N ≥ 196, the sum of Λ(j)(j^(-5/2) − j^(-3)) over N < j ≤ 4N is at least 1/(128 N^(3/2)).
-- source:
--   https://prove2.me/theorems/0748182a-f4f0-40da-bda7-86b30da60594

import Mathlib
open ArithmeticFunction Finset

namespace MasulloRH
theorem prime_tail_reserve_to_four_mul (X : ℕ) (hX : 196 ≤ X) :
    1/(128*(X:ℝ)^(3/2:ℝ)) ≤ ∑ j ∈ Ioc X (4*X),
      (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)) := by sorry
end MasulloRH
