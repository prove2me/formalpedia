-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_squarefree_card_two_eq_two_primes
-- name    : OddPerfectNumber.Kernel.squarefree_card_two_eq_two_primes
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:22:48.259913+00:00
-- url     : https://prove2.me/theorems/04aeb617-292f-4f96-ba00-ac391f0a5fa8
-- title:
--   A square-free number with exactly two prime factors is a product of two distinct primes in increasing order
-- statement:
--   Let $d$ be a square-free natural number with exactly two distinct prime factors. Then $d$ is the product of two distinct primes $q<r$. This is the shape lemma needed to finish the $k=5$ square-free-index reduction $\omega(\mathrm{squarefree\_part}(s)) \ge 3$: once the lower bound $2 \le \#\mathrm{primeFactors}$ is known, a failure of the bound $3$ forces the cardinality to be exactly $2$, and this child turns that into an explicit semiprime $d = q r$ with $q<r$ to hand to the two-prime residual. The pinned Mathlib revision $0df444a360ea$ contains no lemma of the form $\mathrm{squarefree\_and\_primeFactors\_card\_eq\_two\_iff}$, so the characterisation is obtained instead from $\mathrm{Finset.card\_eq\_two}$, which produces an explicit two-element presentation of the finset together with the $q<r$ ordering, and from $\mathrm{Nat.prod\_primeFactors\_of\_squarefree}$, the same square-free product characterisation that the accepted child OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small (64627c09-9af1-4ab3-afc0-a3498abf1dc3) is built on. The two members are automatically distinct because a finset has no duplicates, so no separate injectivity hypothesis is needed.
-- source:
--   Mathlib only: Finset.card_eq_two gives the explicit two-element presentation with the q < r ordering, and Nat.prod_primeFactors_of_squarefree characterises a square-free number as the product of its distinct prime factors. The statement is pure finite-set and factorization bookkeeping with no conjecture-specific content, and it is the exact missing shape step for the accepted sibling OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small (64627c09-9af1-4ab3-afc0-a3498abf1dc3), whose hypothesis hneTwo rules out d = q * r for q < r both prime.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem squarefree_card_two_eq_two_primes {d : Nat} (hdsf : Squarefree d)
    (hcard : d.primeFactors.card = 2) :
    ∃ q r : Nat, q < r ∧ q.Prime ∧ r.Prime ∧ d = q * r := by
  sorry

end OddPerfectNumber.Kernel
