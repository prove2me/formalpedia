-- Prove2me | Theorems.Thm_OddPerfectNumber_exists_two_pow_mul_prime_pow_of_card_odd_primeFactors_le_one
-- name    : OddPerfectNumber.exists_two_pow_mul_prime_pow_of_card_odd_primeFactors_le_one
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:05:39.70109+00:00
-- url     : https://prove2.me/theorems/a49b4ed2-bc27-436d-8d19-22078dc3bae6
-- title:
--   At most one odd prime factor means the shape $2^a q^b$
-- statement:
--   If a non-zero natural number $n$ has at most one odd prime factor, then
--   $$n = 2^a q^b$$
--   for some prime $q$ and some $a, b \ge 0$.
--
--   **Why it is true.** Removing $2$ from $n.\text{primeFactors}$ leaves the odd prime factors. Two cases:
--
--   - The set is empty. Then $n$ has no odd prime factor, so $n = 2^{v_2(n)}$ — including $n = 1$ with $a = 0$. Take any prime for $q$ and $b = 0$; the statement is satisfied with $q$ arbitrary, so it is convenient to pick $q = 3$.
--   - The set is a singleton $\{q\}$. Then the prime factors of $n$ are contained in $\{2, q\}$, so the factorisation $n = \prod_p p^{v_p(n)}$ collapses to $2^{v_2(n)}q^{v_q(n)}$.
--
--   The hypothesis $n \ne 0$ is needed: in Mathlib $0.\text{primeFactors} = \emptyset$, so the cardinality condition holds vacuously at $n = 0$, but $0$ is not of the form $2^aq^b$.
--
--   **What it is for.** In the Dris analysis of odd perfect numbers $N = p^k m^2$, the factorisation of $\sigma(p^k) = \frac{p^{k+1}-1}{p-1}$ is governed by the divisors of $k+1$: each $d \mid k+1$ contributes a cyclotomic factor $\Phi_d(p)$. The branch where $k+1$ has at most one odd prime factor is handled by `OddPerfectNumber.no_dris_one_odd_prime_shaped_core`, which assumes the shape $k+1 = 2^aq^b$ outright. This statement is exactly what converts the cardinality hypothesis of `no_dris_one_odd_prime_core` into that shape, and it is pure elementary number theory — no perfect numbers, no $\sigma$, nothing about $p$ or $m$.
--
--   Separating it out keeps the counting fact about $k+1$ away from the arithmetic of the Dris equations, where it would otherwise have to be re-derived.
-- source:
--   Elementary; the shape hypothesis appears in the exponent analysis of odd perfect numbers, cf. the Dris parametrisation and Broughan-Delbourgo-Zhou style exponent arguments.

import Mathlib

namespace OddPerfectNumber

theorem exists_two_pow_mul_prime_pow_of_card_odd_primeFactors_le_one
    (n : Nat) (hn : n ≠ 0)
    (h : (n.primeFactors.erase 2).card ≤ 1) :
    ∃ a q b : Nat, q.Prime ∧ n = 2 ^ a * q ^ b := by sorry

end OddPerfectNumber
