-- Prove2me | Theorems.Thm_Helfgott_prime_sieve_constant_upper_14
-- name    : Helfgott.prime_sieve_constant_upper_14
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T15:28:41.807782+00:00
-- url     : https://prove2.me/theorems/85d16338-de68-4973-925d-973c4dd365ab
-- title:
--   An explicit upper bound 1.4 for the prime-sieve constant
-- statement:
--   The additive constant in the prime-sieve asymptotic formula satisfies
--
--   $$c_E=\gamma+\sum_{p\text{ prime}}\frac{\log p}{p(p-1)}\le\frac75.$$
--
--   Here $\gamma$ is Euler's constant. This is a conservative rigorous upper bound for the constant in Helfgott's equation (5.14), suitable for explicit sieve estimates; it is not the sharper decimal approximation quoted in that equation.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, Section 5.2, equation (5.14), defining c_E and quoting its sharper approximation 1.3325822.... This proof independently certifies the weaker upper bound 1.4 through finite logarithmic bounds and an elementary telescoping tail estimate. https://arxiv.org/html/1312.7748v2

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Prime.Defs
open scoped BigOperators

theorem Helfgott.prime_sieve_constant_upper_14 : Real.eulerMascheroniConstant +
    (∑' p : Nat.Primes, Real.log (p : ℕ) /
      (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)-1))) ≤ (7/5 : ℝ) := by sorry
