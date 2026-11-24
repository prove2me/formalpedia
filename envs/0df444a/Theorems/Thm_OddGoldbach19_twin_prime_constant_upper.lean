-- Prove2me | Theorems.Thm_OddGoldbach19_twin_prime_constant_upper
-- name    : OddGoldbach19.twin_prime_constant_upper
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:14:27.581452+00:00
-- url     : https://prove2.me/theorems/5f9b4e60-ee94-46c1-9e2c-fa5c76229703
-- title:
--   A tighter finite-product upper bound for the twin-prime constant
-- statement:
--   With the shared factor-two normalization of the twin-prime singular constant,
--   $$C=2\prod_{p>2}\left(1-\frac{1}{(p-1)^2}\right),$$
--   one has $C\le1.3204$. This certified upper bound sharpens the numerical constant used in the campaign's finite-shift second moment estimates.
-- source:
--   Finite partial-product upper-bound method adapted from public Apache2.0 accepted Prove2Me proof91b4ca4a-771c-4be3-88cd-952059ec7610. The larger partial product through2047 and exact rational block certificates yield the tighter bound1.3204. This is an exact finite numerical consequence, not a new prime-distribution theorem.

import Definitions.Def_TaoFivePrimes_SingularSeries

theorem OddGoldbach19.twin_prime_constant_upper :
    TaoFivePrimes.twinPrimeConstant≤(1.3204:ℝ) := by sorry
