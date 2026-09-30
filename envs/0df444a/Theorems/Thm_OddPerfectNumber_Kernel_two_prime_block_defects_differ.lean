-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_two_prime_block_defects_differ
-- name    : OddPerfectNumber.Kernel.two_prime_block_defects_differ
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T20:28:12.287887+00:00
-- url     : https://prove2.me/theorems/bde45950-5a45-4417-b317-f6a1f1690a26
-- title:
--   The two blocks of a q*r square have distinct odd-multiplicity primes
-- statement:
--   Let $q,r$ be distinct primes and let $a,b$ be coprime nonzero natural numbers such that $q r a b$ is a perfect square while neither $a$ nor $b$ is. Then there are primes $\tau_a \mid a$ and $\tau_b \mid b$ occurring to odd multiplicity in $a$ and $b$ respectively, with $\tau_a \ne \	au_b$. This is the *contextual* form of the two-prime parity statement that the $k=5$ square-free-index reduction needs, and it is genuinely stronger than the false global claim that two coprime non-squares each have exactly one odd-multiplicity prime (for $a=15$, $b=77$ the odd supports are $\{3,5\}$ and $\{7,11\}$). The square relation is what supplies the missing constraint: by the accepted child OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a (89d076b4-d7b5-4a1d-a263-55ad181d1569) every odd-multiplicity prime of $a$ lies in $\{q,r\}$, and applying the same lemma to the exchanged pair $(b,a)$ gives the same containment for $b$. Both supports are therefore nonempty subsets of a two-element set; coprimality, which rules out a common prime via $\mathrm{dvd\_gcd}$ and $\mathrm{Prime.one\_lt}$, forces them to be disjoint, so each is a singleton and the two singletons differ. The forcing step uses the child OddPerfectNumber.Kernel.odd_mult_prime_exists, that a non-square has a prime of odd multiplicity.
-- source:
--   The accepted children OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a (89d076b4-d7b5-4a1d-a263-55ad181d1569) and OddPerfectNumber.Kernel.odd_mult_prime_exists (ffeb6765-ce67-43db-a9b6-5073e23eccdf), together with Mathlib's Nat.dvd_gcd and Nat.Prime.one_lt. Pure exponent-parity bookkeeping inside the q*r square context; it encodes no conjecture-specific content and no deep Diophantine input.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem two_prime_block_defects_differ {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (hna : ¬ ∃ y, y ^ 2 = a) (hnb : ¬ ∃ y, y ^ 2 = b) :
    ∃ ta tb : Nat, ta.Prime ∧ tb.Prime ∧ ta ∣ a ∧ tb ∣ b ∧
      ¬ Even (a.factorization ta) ∧ ¬ Even (b.factorization tb) ∧ ta ≠ tb := by
  sorry

end OddPerfectNumber.Kernel
