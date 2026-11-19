-- Prove2me | Theorems.Thm_MersenneLPW_infinitely_many_even_perfect_numbers
-- name    : MersenneLPW.infinitely_many_even_perfect_numbers
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T15:25:42.602692+00:00
-- url     : https://prove2.me/theorems/1f427393-c886-4b2b-a349-bdc828f50aab
-- title:
--   Infinitude of even perfect numbers
-- statement:
--   There are infinitely many **even perfect numbers**: natural numbers $n$ with $2 \mid n$, $n > 0$, and
--   $$\sum_{\substack{d \mid n \\ d < n}} d \;=\; n.$$
--   Equivalently, by the Euclid–Euler theorem, there are infinitely many Mersenne primes. This is the perfect-number formulation of the mission's goal and is open. It is distinct from the existence question for odd perfect numbers (also open), and it implies the infinitude of all perfect numbers.
--
--   **Formalization Note.** `Nat.Perfect n` is Mathlib's predicate (the sum of the proper divisors of $n$ equals $n$, with $0 < n$ bundled); the set ranges over all naturals, with evenness and perfection as the only filters.
-- source:
--   https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem ; https://en.wikipedia.org/wiki/List_of_Mersenne_primes_and_perfect_numbers ; infinitude open: https://en.wikipedia.org/wiki/Mersenne_prime

import Mathlib

namespace MersenneLPW

theorem infinitely_many_even_perfect_numbers :
    {n : ℕ | Even n ∧ Nat.Perfect n}.Infinite := by sorry

end MersenneLPW
