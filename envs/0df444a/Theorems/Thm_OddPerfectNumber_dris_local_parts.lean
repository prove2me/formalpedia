-- Prove2me | Theorems.Thm_OddPerfectNumber_dris_local_parts
-- name    : OddPerfectNumber.dris_local_parts
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T19:35:08.817896+00:00
-- url     : https://prove2.me/theorems/825801de-3899-429f-bcc9-bd609d8b606e
-- title:
--   Exact local decomposition of a Dris configuration
-- statement:
--   Let $p$ be a prime, let $m$ be odd with $p \nmid m$, and consider the Dris parametrisation of the Euler equation,
--
--   $$2m^2 = \sigma(p^k)\,s, \qquad \sigma(m^2) = p^k s .$$
--
--   For a prime $q \mid m$ write $F(q) = \sigma\!\left(q^{2v_q(m)}\right) = 1 + q + \dots + q^{2v_q(m)}$ for the local divisor sum of $m^2$ at $q$, and split it into its $p$-part and its $p$-free part. Then
--
--   $$\sum_{q \mid m} v_p\bigl(F(q)\bigr) = k, \qquad \prod_{q \mid m} \frac{F(q)}{p^{\,v_p(F(q))}} = s .$$
--
--   In words: the $p$-valuations of the local divisor sums add up to exactly the special exponent $k$, and their $p$-free parts multiply to exactly the Dris index $s$. Both identities are exact, not merely inequalities.
--
--   This is the structural identity behind the known counting bounds for the prime support of $m$ (for instance $\omega(m) \le k + \Omega(s)$, which follows because at most $k$ local sums can have a nontrivial $p$-part while every other one contributes a factor $> 1$ of $s$). Isolating it makes those bounds, and the finer bookkeeping needed for a composite index, available in a single reusable statement.
--
--   *Formalization note.* $\operatorname{ordCompl}[p]\,n$ denotes the $p$-free part $n / p^{v_p(n)}$, and $v_p$ is `Nat.factorization`.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation); the decomposition is the exact form of the counting argument behind OddPerfectNumber.dris_prime_support_bound.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem dris_local_parts (p k m s : Nat) (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    (∑ q ∈ m.primeFactors,
        (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i).factorization p) = k ∧
      (∏ q ∈ m.primeFactors,
        ordCompl[p] (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)) = s := by
  sorry

end OddPerfectNumber
