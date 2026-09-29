-- Prove2me | Theorems.Thm_OddPerfectNumber_no_odd_perfect_special_exponent_ge_five
-- name    : OddPerfectNumber.no_odd_perfect_special_exponent_ge_five
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-08T09:09:56.853598+00:00
-- url     : https://prove2.me/theorems/c603f920-c1c2-4cd9-a69f-2e3bc7a77bc1
-- title:
--   Odd perfect number conjecture, special-exponent case $k \ge 5$
-- statement:
--   Euler proved that an odd perfect number $N$ must have the shape
--   $$N = p^{k} m^{2},$$
--   where $p$ is prime, $p \equiv k \equiv 1 \pmod 4$, and $p \nmid m$. The prime $p$ is called the *special* (or *Euler*) prime of $N$, and $k$ its special exponent.
--
--   Since $k \equiv 1 \pmod 4$, either $k = 1$ or $k \ge 5$. This theorem is the nonexistence assertion in the second of those two cases:
--
--   there are no natural numbers $N$, $p$, $k$, $m$ with $N$ perfect and odd, $p$ prime, $p \equiv 1 \pmod 4$, $k \equiv 1 \pmod 4$, $k \ge 5$, $p \nmid m$, and
--   $$N = p^{k} m^{2}.$$
--
--   This is the case complementary to the one asserted by the Descartes-Frenicle-Sorli conjecture, which predicts $k = 1$ for every odd perfect number. Together with Euler's structure theorem and the statement for $k = 1$, this theorem yields the Odd Perfect Number Conjecture; each of the two cases is open.
--
--   **Formalization Note** Perfection is `Nat.Perfect`, i.e. the proper divisors of $N$ sum to $N$ and $N > 0$. The congruences are written as `p % 4 = 1` and `k % 4 = 1`; the hypothesis $k \ge 5$ is kept alongside `k % 4 = 1` so that the statement is exactly the complement of the case $k = 1$. The conclusion is stated as the inequation $N \ne p^{k} m^{2}$ under the stated hypotheses.
-- source:
--   Case split of the Odd Perfect Number Conjecture along Euler's structure theorem for odd perfect numbers (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849), 88-101). Statement of Euler's theorem and of the conjecture as recorded in https://en.wikipedia.org/wiki/Perfect_number, section 'Odd perfect numbers' (N = q^alpha p_1^{2e_1} ... p_k^{2e_k} with q prime and q = alpha = 1 mod 4). The case alpha = 1 is the case asserted by the Descartes-Frenicle-Sorli conjecture; see J. A. B. Dris, 'The abundancy index of divisors of odd perfect numbers', Journal of Integer Sequences 15 (2012), Article 12.4.4, https://cs.uwaterloo.ca/journals/JIS/VOL15/Dris/dris8.html, Conjecture 1.

import Mathlib

namespace OddPerfectNumber

theorem no_odd_perfect_special_exponent_ge_five (n p k m : ℕ) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk5 : 5 ≤ k) (hpm : ¬ p ∣ m) :
    n ≠ p ^ k * m ^ 2 := by
  sorry

end OddPerfectNumber
