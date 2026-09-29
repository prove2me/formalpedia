-- Prove2me | Theorems.Thm_OddPerfectNumber_special_pow_lt_sq_of_exponent_ge_five
-- name    : OddPerfectNumber.special_pow_lt_sq_of_exponent_ge_five
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-08T21:33:45.719726+00:00
-- url     : https://prove2.me/theorems/0844af37-d380-4609-822b-a0fe76d03bdf
-- title:
--   Odd perfect numbers with special exponent $k \ge 5$ satisfy $p^k < m^2$
-- statement:
--   Let $N$ be an odd perfect number written in Euler form,
--
--   $$N = p^{k}m^{2}, \qquad p \text{ prime},\ p \nmid m,$$
--
--   and suppose the special exponent satisfies $k \equiv 1 \pmod 4$ and $k \ge 5$. Then the special part is strictly smaller than the square part:
--
--   $$p^{k} \;<\; m^{2}.$$
--
--   **Context.** Euler's structure theorem says that every odd perfect number has this shape with $p \equiv k \equiv 1 \pmod 4$; the Descartes–Frenicle–Sorli conjecture asserts that $k = 1$ always, and the case $k \ge 5$ is open. Comparing the sizes of the two parts $p^{k}$ and $m^{2}$ is a standard line of attack on that conjecture. The statement above settles the comparison for every special exponent $k \ge 5$: the special part can never dominate. Equivalently, in the parametrisation $2m^{2} = \sigma(p^{k})s$, $\sigma(m^{2}) = p^{k}s$ of the Euler equation, the index $s$ is never equal to $1$ when $k \ge 5$.
--
--   Consequently no odd perfect number of the form $p^{k}m^{2}$ with $k \equiv 1 \pmod 4$, $k \ge 5$, $p \nmid m$ and $m^{2} \le p^{k}$ exists at all.
-- source:
--   Comparison of the two parts of an odd perfect number in Euler form; the parametrisation used is that of J. A. B. Dris, 'The abundancy index of divisors of odd perfect numbers', Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2. The statement here is the case k >= 5 of the size comparison p^k versus m^2.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem special_pow_lt_sq_of_exponent_ge_five (n p k m : ℕ) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hk4 : k % 4 = 1) (hk5 : 5 ≤ k) (hpm : ¬ p ∣ m) (hnpm : n = p ^ k * m ^ 2) :
    p ^ k < m ^ 2 := by sorry

end OddPerfectNumber
