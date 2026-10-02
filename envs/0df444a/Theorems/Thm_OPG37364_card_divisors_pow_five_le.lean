-- Prove2me | Theorems.Thm_OPG37364_card_divisors_pow_five_le
-- name    : OPG37364.card_divisors_pow_five_le
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T06:18:25.487217+00:00
-- url     : https://prove2.me/theorems/2df82027-2123-4660-89a0-feef867a1e9f
-- title:
--   Explicit fifth-power bound for the number of positive divisors
-- statement:
--   For every positive integer n, let τ(n) denote the number of its positive divisors. Then τ(n)^5 ≤ 512^32 n. This is an explicit natural-number estimate, with a single constant valid for all positive n. It follows from the prime-factorization product for τ, the inequalities (e+1)^5 ≤ 32^e and (e+1)^5 ≤ 512·2^e, and a bound of 32 on the number of prime factors below 32. No classification of the small primes, asymptotic premise, or unproved representation-count estimate is assumed.
-- source:
--   OPG37364 arithmetic sprint: elementary explicit-constant divisor estimate using Mathlib Nat.card_divisors and Nat.prod_primeFactors_pow_factorization. Formalization of a classical divisor-function bound; no mathematical novelty claimed. Existing Formalpedia CircleMethod.divisor_bound_pow (2a78a165-a186-4ccc-833c-fcba09d9fc6f) supplies an existential arbitrary-epsilon estimate; the present theorem specifies the explicit natural constant 512^32 and is independently proved directly in the pinned environment.

import Mathlib.NumberTheory.ArithmeticFunction.Misc
set_option autoImplicit false

namespace OPG37364
theorem card_divisors_pow_five_le (n : ℕ) (hn : 0 < n) :
    n.divisors.card ^ 5 ≤ 512^32 * n := by sorry
end OPG37364
