-- Prove2me | Theorems.Thm_Helfgott_twinPrimeConstant_lower
-- name    : Helfgott.twinPrimeConstant_lower
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T01:17:54.189199+00:00
-- url     : https://prove2.me/theorems/ce2e80e9-580a-4ca9-82ac-1407b62f0739
-- title:
--   Explicit lower bound 1.32 for the twin-prime Euler constant
-- statement:
--   For the Euler constant
--
--   $$\mathfrak S_2=2\prod_{p>2}\left(1-\frac1{(p-1)^2}\right),$$
--
--   where the product runs over odd primes, one has
--
--   $$\mathfrak S_2\ge\frac{33}{25}=1.32.$$
--
--   This is the normalization with the leading factor $2$. It is useful in explicit prime-pair sieve estimates and as a uniform lower comparison for the ternary Goldbach singular series. The rational bound is coarser than the sharper numerical constant in Helfgott's paper.
--
--   Formalization note: the existing definition represents the constant as twice the infimum of its finite partial products.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, equation (7.10); T. Tao, Every odd number greater than 1 is the sum of at most five primes, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10. The coarser rational constant 1.32 is derived from explicit finite certificates and a complete elementary tail bound in the accompanying proof. Written by Codex.

import Definitions.Def_TaoFivePrimes_SingularSeries

theorem Helfgott.twinPrimeConstant_lower : (33/25:ℝ) ≤ TaoFivePrimes.twinPrimeConstant := by sorry
