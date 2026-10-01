-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_squarefree_card_two_from_ge_two_and_not_three
-- name    : OddPerfectNumber.Kernel.squarefree_card_two_from_ge_two_and_not_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T13:08:43.118716+00:00
-- url     : https://prove2.me/theorems/5632e718-2955-4324-b529-33cfab141555
-- title:
--   A square-free number with at least two and fewer than three prime factors is a product of two distinct primes
-- statement:
--   Let $d$ be a square-free natural number. If $d$ has at least two distinct prime factors and fewer than three, then $d$ is the product of two distinct primes: there exist $q < r$ with $q$ and $r$ prime and $d = q r$.
--
--   This is pure finite-set bookkeeping. The hypotheses $2 \le d.\omega$ and $\neg 3 \le d.\omega$ pin the cardinality to exactly $2$, and `OddPerfectNumber.Kernel.squarefree_card_two_eq_two_primes` (04aeb617-292f-4f96-ba00-ac391f0a5fa8, Proved) then produces the ordered pair. The generic sibling `OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small` (64627c09-9af1-4ab3-afc0-a3498abf1dc3, Proved) uses the same characterisation for the bound of three.
--
--   This is the structural bridge used in the $k = 5$ Dris branch: once the lower bound $\omega(d_2) \ge 2$ is available, a failure of $\omega(d_2) \ge 3$ forces the square-free part of the index to be exactly a product of two distinct primes, which is the shape the remaining hard residual must exclude.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem squarefree_card_two_from_ge_two_and_not_three {d : Nat} (hdsf : Squarefree d) (hge2 : 2 ≤ d.primeFactors.card)
    (hnge3 : ¬ 3 ≤ d.primeFactors.card) :
    ∃ q r : Nat, q < r ∧ q.Prime ∧ r.Prime ∧ d = q * r := by
  sorry

end OddPerfectNumber.Kernel
