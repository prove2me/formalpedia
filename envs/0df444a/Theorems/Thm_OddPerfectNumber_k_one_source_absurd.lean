-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_source_absurd
-- name    : OddPerfectNumber.k_one_source_absurd
-- status  : Open
-- author  : @WillR
-- created : 2026-09-11T09:07:20.89932+00:00
-- url     : https://prove2.me/theorems/888a1c5b-43ba-4548-bb2a-2df4d5a1c26b
-- title:
--   The unique-source configuration for k = 1 is impossible
-- statement:
--   Let $p$ be prime with $p \equiv 1 \pmod 4$ and $m \ge 2$ odd with $p \nmid m$, with packaged identities $m^2 = td$ and $\sigma(m^2) = pd$ for $t = (p+1)/2$. Suppose further that a distinguished prime $q$ in the support of $m^2$ carries $p$ in its local divisor sum, and that no other prime of the support does. Then this configuration is impossible. This is the research core of the $k = 1$ case after all proved packaging, valuation, and unique-source steps: the remaining content is the multiplicative-order and cyclotomic restriction on the distinguished prime.
-- source:
--   Valuation-flow endgame of the special-exponent k = 1 case of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem k_one_source_absurd (p m d q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (hm2 : 2 ≤ m)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q) :
    False := by
  sorry

end OddPerfectNumber
