-- Prove2me | Theorems.Thm_OddPerfectNumber_euler_form
-- name    : OddPerfectNumber.euler_form
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T20:15:10.1453+00:00
-- url     : https://prove2.me/theorems/ce498e6e-9abd-42ab-98a6-b7d54a53b45f
-- title:
--   Euler's form of an odd perfect number
-- statement:
--   **Euler's theorem on odd perfect numbers (1849).** Suppose $N$ is an odd perfect number, i.e. $N$ is odd and $\sigma(N) = 2N$, where $\sigma$ is the sum-of-divisors function. Then $N$ has the shape
--   $$N = p^{k} m^{2},$$
--   where $p$ is a prime with $p \equiv 1 \pmod 4$, the exponent satisfies $k \equiv 1 \pmod 4$, and $p \nmid m$. The prime power $p^{k}$ is called the *special* (or *Euler*) *component* of $N$; the remaining part $m^2$ is a square, and it is coprime to $p$.
--
--   The statement is formalized for natural numbers, with perfection given by Mathlib's `Nat.Perfect` (which includes positivity) and the congruences written as `p % 4 = 1` and `k % 4 = 1`. Note that $m$ is automatically odd, since $N$ is.
-- source:
--   L. Euler, De numeris amicabilibus, Commentationes arithmeticae 2 (1849), 627-636; see also https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers (Euler's form).

import Mathlib

namespace OddPerfectNumber

theorem euler_form (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) :
    ∃ p k m : ℕ, p.Prime ∧ p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m ∧ n = p ^ k * m ^ 2 := by
  sorry

end OddPerfectNumber
