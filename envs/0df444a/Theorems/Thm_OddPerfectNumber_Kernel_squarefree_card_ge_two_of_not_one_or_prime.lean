-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_squarefree_card_ge_two_of_not_one_or_prime
-- name    : OddPerfectNumber.Kernel.squarefree_card_ge_two_of_not_one_or_prime
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:11:16.879429+00:00
-- url     : https://prove2.me/theorems/9c90129e-60c2-4fa1-aa32-c55ece1e485d
-- title:
--   A square-free number that is not 1 and not a prime has at least two prime factors
-- statement:
--   Let $d$ be a positive square-free natural number. If $d$ is neither $1$ nor a prime, then $d$ has at least two distinct prime factors, i.e. $\#\mathrm{primeFactors}(d) \ge 2$. This is the $\ge 2$ counterpart of the accepted child OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small (64627c09-9af1-4ab3-afc0-a3498abf1dc3) and is written in the same idiom, so the two compose directly. Mathlib in the pinned revision $0df444a360ea$ has no lemma of the form $\mathrm{squarefree\_and\_primeFactors\_card\_eq\_two\_iff}$, so the $\ge 2$ bound has to be obtained from the same characterisation the accepted $\ge 3$ child uses: a square-free number is the product of its distinct prime factors, by $\mathrm{Nat.prod\_primeFactors\_of\_squarefree}$. Assuming the cardinality is at most one and splitting on whether it is zero or positive, the empty case makes that product empty and forces $d=1$, and the singleton case makes it a single prime. Both contradict the hypotheses. This is the step that turns the Dris-index square-free kernel from 'not a square' and 'not a single prime' into a genuine lower bound of two on the number of distinct prime factors, which is the first step of the $k=5$ reduction $\omega(\mathrm{squarefree\_part}(s)) \ge 3$.
-- source:
--   Mathlib only: Nat.prod_primeFactors_of_squarefree characterises a square-free number as the product of its distinct prime factors, and Finset.card_eq_one unpacks the singleton case. The statement and proof are pure finite-set and factorization bookkeeping with no conjecture-specific content; the accepted sibling OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small (64627c09-9af1-4ab3-afc0-a3498abf1dc3) uses exactly the same characterisation for the corresponding bound of three.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem squarefree_card_ge_two_of_not_one_or_prime {d : Nat} (hdpos : 0 < d)
    (hdsf : Squarefree d) (hne1 : d ≠ 1) (hnePrime : ∀ q, q.Prime → d ≠ q) :
    2 ≤ d.primeFactors.card := by
  sorry

end OddPerfectNumber.Kernel
