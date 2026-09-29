-- Prove2me | Theorems.Thm_OddPerfectNumber_no_euler_equation_special_exponent_ge_nine
-- name    : OddPerfectNumber.no_euler_equation_special_exponent_ge_nine
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-08T11:14:28.268701+00:00
-- url     : https://prove2.me/theorems/d5966631-88d0-4426-b193-0cc25fa1a415
-- title:
--   Euler equation for an odd perfect number with special exponent $k \\ge 9$ has no solution
-- statement:
--   Write $\sigma(n)=\sum_{d\mid n} d$ for the sum-of-divisors function.
--
--   Let $p$ be a prime with $p \equiv 1 \pmod 4$, let $k$ be a natural number with $k \equiv 1 \pmod 4$ and $k \ge 9$, and let $m$ be an odd natural number with $p \nmid m$. The assertion is that
--
--   $$\sigma(p^{k})\,\sigma(m^{2}) \neq 2\,p^{k}m^{2}.$$
--
--   Since $p^{k}$ and $m^{2}$ are coprime and $\sigma$ is multiplicative, the displayed equation says exactly that $N = p^{k}m^{2}$ satisfies $\sigma(N) = 2N$, i.e. that $N$ is an odd perfect number written in Euler's form with special (Euler) prime $p$ and special exponent $k$. Together with the case $k = 5$, this covers every special exponent $k \equiv 1 \pmod 4$ with $k \ge 5$, that is, the whole complement of the case $k = 1$ predicted by the Descartes-Frenicle-Sorli conjecture.
--
--   **Formalization Note** Perfection is expressed directly through the divisor-sum equation $\sigma(p^{k})\sigma(m^{2}) = 2p^{k}m^{2}$ rather than through `Nat.Perfect`; the two are equivalent here because $p^{k}$ and $m^{2}$ are coprime and $N = p^{k}m^{2} > 0$ is odd. The congruences are written as `p % 4 = 1` and `k % 4 = 1`, and the sum-of-divisors function as an explicit sum over `Nat.divisors`.
-- source:
--   Subcase k >= 9 of the special-exponent case of the Odd Perfect Number Conjecture, via Euler's structure theorem for odd perfect numbers (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849), 88-101): N = q^alpha p_1^{2e_1} ... p_k^{2e_k} with q prime and q = alpha = 1 mod 4, as recorded in https://en.wikipedia.org/wiki/Perfect_number, section 'Odd perfect numbers'. The exponent alpha = 1 case is the Descartes-Frenicle-Sorli conjecture; see J. A. B. Dris, 'The abundancy index of divisors of odd perfect numbers', Journal of Integer Sequences 15 (2012), Article 12.4.4, Conjecture 1.

import Mathlib

namespace OddPerfectNumber

theorem no_euler_equation_special_exponent_ge_nine (p k m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hk4 : k % 4 = 1) (hk9 : 9 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m) :
    (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) ≠ 2 * (p ^ k * m ^ 2) := by
  sorry

end OddPerfectNumber
