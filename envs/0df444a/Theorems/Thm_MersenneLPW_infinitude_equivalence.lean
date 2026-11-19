-- Prove2me | Theorems.Thm_MersenneLPW_infinitude_equivalence
-- name    : MersenneLPW.infinitude_equivalence
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T15:25:27.991517+00:00
-- url     : https://prove2.me/theorems/2dee07f1-c043-4d4a-98f5-c8beae3d03ab
-- title:
--   Infinitude of Mersenne primes $\iff$ infinitude of even perfect numbers
-- statement:
--   The set of exponents $p$ for which $2^p - 1$ is prime is infinite **if and only if** the set of even perfect numbers is infinite. This is the precise form of the classical observation that the questions 'are there infinitely many Mersenne primes?' and 'are there infinitely many even perfect numbers?' are equivalent, via the one-to-one correspondence of the Euclid–Euler theorem. Both sides are open; the equivalence itself is a provable statement and records that the two formulations stand or fall together.
--
--   **Formalization Note.** The left-hand set is exactly the goal theorem's set (`FCP.Mersenne.infinitely_many_mersenne_primes`); `mersenne p = 2 ^ p - 1`; `Nat.Perfect` includes positivity; `Even n` is Mathlib's evenness predicate. The statement is an `↔` of two `Set.Infinite` claims, not a one-sided implication.
-- source:
--   Consequence of the Euclid–Euler theorem (Euclid, Elements IX.36; Euler 1747/1849): https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem ; 'a one-to-one correspondence between even perfect numbers and Mersenne primes': https://en.wikipedia.org/wiki/Mersenne_prime

import Mathlib

namespace MersenneLPW

theorem infinitude_equivalence :
    {p : ℕ | (mersenne p).Prime}.Infinite ↔ {n : ℕ | Even n ∧ Nat.Perfect n}.Infinite := by sorry

end MersenneLPW
