-- Prove2me | Theorems.Thm_MersenneLPW_euclid_euler
-- name    : MersenneLPW.euclid_euler
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T15:25:12.87893+00:00
-- url     : https://prove2.me/theorems/6f52d603-fe9f-4a55-a00a-c526be7902c0
-- title:
--   Euclid–Euler theorem (characterization of even perfect numbers)
-- statement:
--   Let $n$ be a natural number. Then $n$ is **even and perfect** — $2 \mid n$, $n > 0$, and the sum of the proper divisors of $n$ equals $n$ — if and only if there is a natural number $k$ such that $2^{k+1} - 1$ is prime and
--   $$n = 2^{k}\,(2^{k+1} - 1).$$
--   Writing $p = k+1$, this is the classical statement that the even perfect numbers are exactly the numbers $2^{p-1}(2^p - 1)$ with $2^p - 1$ a Mersenne prime. The forward implication (Euclid's construction) is *Elements* IX.36; the converse is Euler's theorem, read to the Berlin Academy in 1747 and published posthumously in 1849.
--
--   This characterization is the bridge between Mersenne primes and perfect numbers: it is the basis for the equivalence of their infinitude assertions in this mission.
--
--   **Formalization Note.** `mersenne p = 2 ^ p - 1` is Mathlib's Mersenne number; `Nat.Perfect n` bundles the positivity requirement $0 < n$. The exponent is written $k + 1$ rather than $p$ with $p - 1$, avoiding truncated natural-number subtraction; the statement mirrors Mathlib's Archive theorem `Theorems100.Nat.even_and_perfect_iff`.
-- source:
--   Euclid, Elements IX.36 (forward direction); L. Euler, converse read to the Berlin Academy 23 Feb 1747, published posthumously 1849 (https://mathworld.wolfram.com/Euclid-EulerTheorem.html). Statement mirrors mathlib4 Archive/Wiedijk100Theorems/PerfectNumbers.lean, theorem Theorems100.Nat.even_and_perfect_iff, rev 0df444a360eaa60ab8c11dca51a86af692955474: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Archive/Wiedijk100Theorems/PerfectNumbers.lean ; overview https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem

import Mathlib

namespace MersenneLPW

theorem euclid_euler (n : ℕ) :
    Even n ∧ Nat.Perfect n ↔
      ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by sorry

end MersenneLPW
