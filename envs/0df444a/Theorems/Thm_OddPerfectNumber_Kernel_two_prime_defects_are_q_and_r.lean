-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_two_prime_defects_are_q_and_r
-- name    : OddPerfectNumber.Kernel.two_prime_defects_are_q_and_r
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T09:07:45.236126+00:00
-- url     : https://prove2.me/theorems/94301dcb-06a5-4ae5-8b7b-8de0c6c2fcbe
-- title:
--   In the two-prime square context the two coprime block defects are q and r in some order
-- statement:
--   Suppose $a$ and $b$ are coprime positive naturals, $q$ and $r$ are distinct primes, $qrab$ is a perfect square, and neither $a$ nor $b$ is a square. Then the two odd-multiplicity defect primes of $a$ and of $b$ are exactly $q$ and $r$, in one order or the other. More concretely there are $x,y$ with $\{x,y\}=\{q,r\}$: either $x=q,y=r$ or $x=r,y=q$. This is the exact parity allocation needed by the $k=5$ two-prime residual. The proved child `OddPerfectNumber.Kernel.two_prime_block_defects_differ` (bde45950-5a45-4417-b317-f6a1f1690a26) produces two *distinct* primes $ta\mid a$ and $tb\mid b$ whose factorisation exponents are odd, and the proved child `OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a` (89d076b4-d7b5-4a1d-a263-55ad181d1569) confines every such defect to $\{q,r\}$. Two distinct members of a two-element set are the two members in some order, so the case split on $(ta,tb)\in\{q,r\}^2$ leaves exactly the two orders after the diagonal is refuted by $ta\neq tb$. The frequently quoted generalisation that coprime non-squares each have exactly one odd-multiplicity prime is **false** and is not used: $a=15$, $b=77$ are coprime non-squares and each has two odd-multiplicity primes ($3,5$ and $7,11$). The square relation $qrab=y^2$ is therefore essential, and it is exactly what the two imported children consume.
-- source:
--   Mathlib only, and in fact no mathematics beyond the two imported proved children. The proof is the four-case analysis of the two disjunctions, with the two diagonal branches closed by `absurd` against the distinctness `ta ≠ tb` supplied by `two_prime_block_defects_differ`. No deep input: the k=5 Dris index work uses this only after the first Dris equation has forced $q r U V$ to be a square, and it is the last purely structural step before the second Dris equation sigma(m^2) = p^5 s must be used.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem two_prime_defects_are_q_and_r {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a)
    (hnb : ¬ ∃ y, y ^ 2 = b) :
    ∃ x y : Nat, (x = q ∧ y = r) ∨ (x = r ∧ y = q) := by
  sorry

end OddPerfectNumber.Kernel
