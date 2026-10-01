-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_cyclotomic_split
-- name    : OddPerfectNumber.Kernel.five_two_prime_cyclotomic_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T14:11:54.867981+00:00
-- url     : https://prove2.me/theorems/81a70179-c0e7-41e8-97bd-86af2cb90f91
-- title:
--   In the $k = 5$ two-prime case the two distinct primes split between the two cyclotomic blocks
-- statement:
--   Let $p \ge 5$ be a prime with $p \equiv 1 \pmod 4$, let $m$ be odd with $p \nmid m$, and let $q < r$ be distinct primes. Suppose the first $k = 5$ Dris equation holds with the index $s = d_1^2 q r$, i.e. $2m^2 = \sigma(p^5) d_1^2 q r$ with $\sigma(p^5) = 2(p^2+p+1)\left(\frac{p+1}{2}\right)(p^2-p+1)$. Then the prime $q$ or the prime $r$ is the unique odd-multiplicity prime of the first cyclotomic block $p^2 + p + 1$: in either case $p^2+p+1$ equals that prime times a square.
--
--   The argument is the parity allocation that the Proved children `OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a` (89d076b4-d7b5-4a1d-a263-55ad181d1569) and `OddPerfectNumber.Kernel.two_prime_defects_are_q_and_r` (94301dcb-06a5-4ae5-8b7b-8de0c6c2fcbe) already provide. The first Dris equation makes $m^2 = d_1^2 q r U V$ a square with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$. Since $U$ and $V$ are coprime and both non-squares, each has a nonempty odd-multiplicity prime support, the two supports are disjoint, and both are contained in $\{q, r\}$. Two disjoint nonempty subsets of a two-element set are singletons, so exactly one of $q, r$ is the odd-multiplicity defect of $U$ and the other of $V$.
--
--   Only the first Dris equation is used, which is legitimate: this statement is a necessary structural consequence of the parity bookkeeping, not a contradiction. The remaining contradiction against the second Dris equation is the open residual `OddPerfectNumber.Kernel.five_no_two_prime_squarefree_index` (6eb10265-4d2f-4227-b550-4a6ccf0d94b3).

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_cyclotomic_split (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime)
    (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    (∃ x, p ^ 2 + p + 1 = q * x ^ 2) ∨ (∃ x, p ^ 2 + p + 1 = r * x ^ 2) := by
  sorry

end OddPerfectNumber.Kernel
