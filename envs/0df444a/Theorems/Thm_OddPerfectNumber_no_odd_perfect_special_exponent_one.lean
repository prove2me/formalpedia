-- Prove2me | Theorems.Thm_OddPerfectNumber_no_odd_perfect_special_exponent_one
-- name    : OddPerfectNumber.no_odd_perfect_special_exponent_one
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-08T09:09:58.509242+00:00
-- url     : https://prove2.me/theorems/e38af2be-743b-477a-a54e-10368eafebd3
-- title:
--   Odd perfect number conjecture, special-exponent case $k = 1$
-- statement:
--   Euler proved that an odd perfect number $N$ must have the shape
--   $$N = p^{k} m^{2},$$
--   where $p$ is prime, $p \equiv k \equiv 1 \pmod 4$, and $p \nmid m$. The prime $p$ is called the *special* (or *Euler*) prime of $N$, and $k$ its special exponent.
--
--   Since $k \equiv 1 \pmod 4$, either $k = 1$ or $k \ge 5$. This theorem is the nonexistence assertion in the first of those two cases:
--
--   there are no natural numbers $N$, $p$, $m$ with $N$ perfect and odd, $p$ prime, $p \equiv 1 \pmod 4$, $p \nmid m$, and
--   $$N = p\,m^{2}.$$
--
--   The configuration $k = 1$ is exactly the one asserted to hold for every odd perfect number by the Descartes-Frenicle-Sorli conjecture, and a substantial part of the literature on odd perfect numbers treats it separately from the case $k \ge 5$. Together with Euler's structure theorem and the complementary statement for $k \ge 5$, this theorem yields the Odd Perfect Number Conjecture; each of the two cases is open.
--
--   **Formalization Note** Perfection is `Nat.Perfect`, i.e. the proper divisors of $N$ sum to $N$ and $N > 0$. The congruences are written as `p % 4 = 1`, and the conclusion is stated as the inequation $N \ne p\,m^{2}$ under the stated hypotheses.
-- source:
--   Case split of the Odd Perfect Number Conjecture along Euler's structure theorem for odd perfect numbers (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849), 88-101). Statement of Euler's theorem and of the conjecture as recorded in https://en.wikipedia.org/wiki/Perfect_number, section 'Odd perfect numbers' (N = q^alpha p_1^{2e_1} ... p_k^{2e_k} with q prime and q = alpha = 1 mod 4). The case alpha = 1 is the case asserted by the Descartes-Frenicle-Sorli conjecture; see J. A. B. Dris, 'The abundancy index of divisors of odd perfect numbers', Journal of Integer Sequences 15 (2012), Article 12.4.4, https://cs.uwaterloo.ca/journals/JIS/VOL15/Dris/dris8.html, Conjecture 1.

import Mathlib

namespace OddPerfectNumber

theorem no_odd_perfect_special_exponent_one (n p m : ℕ) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) : n ≠ p * m ^ 2 := by
  sorry

end OddPerfectNumber
