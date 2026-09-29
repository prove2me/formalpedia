-- Prove2me | Theorems.Thm_OddPerfectNumber_not_isSquare
-- name    : OddPerfectNumber.not_isSquare
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T20:15:27.715052+00:00
-- url     : https://prove2.me/theorems/c9140301-35c0-4f34-9e0d-afb59c8a7a33
-- title:
--   An odd perfect number is not a perfect square
-- statement:
--   **Corollary of Euler's form.** No odd perfect number is a perfect square. Concretely, if $N$ is odd and $\sigma(N) = 2N$, then there is no $r$ with $N = r^2$.
--
--   One route is through Euler's form $N = p^k m^2$ with $k \equiv 1 \pmod 4$: the exponent of the special prime $p$ is odd, so $N$ cannot be a square. A second, self-contained route uses the parity of $\sigma$: for odd $N$, $\sigma(N)$ is odd precisely when $N$ is a square, whereas $\sigma(N) = 2N$ is even.
--
--   Formalized with Mathlib's `IsSquare` predicate on `ℕ`.
-- source:
--   Corollary of Euler's form; see https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers .

import Mathlib

namespace OddPerfectNumber

theorem not_isSquare (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) : ¬ IsSquare n := by
  sorry

end OddPerfectNumber
