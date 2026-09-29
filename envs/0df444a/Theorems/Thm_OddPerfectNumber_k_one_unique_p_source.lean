-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_unique_p_source
-- name    : OddPerfectNumber.k_one_unique_p_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T07:51:43.054887+00:00
-- url     : https://prove2.me/theorems/fc480539-7a90-4164-9c79-8429d1606d26
-- title:
--   Exactly one prime-power divisor sum supplies the factor p
-- statement:
--   Let $p$ be prime and suppose the divisor sum of the square $m^2$ factors as $\sigma(m^2) = pd$ with exact $p$-adic valuation one. Then exactly one prime divisor $q$ of $m^2$ has $p$ dividing its local divisor sum $\sigma(q^{v_q(m^2)}) = 1 + q + \cdots + q^{v_q(m^2)}$. Indeed $\sigma$ is multiplicative over the coprime prime-power factors of $m^2$, so $v_p(\sigma(m^2))$ is the sum of the local valuations; a sum of naturals equal to one means exactly one of them is one. This is step 5 of the factor-chain attack: the unique prime-power component supplying the single factor $p$, the target on which the multiplicative-order and quadratic-residue restrictions (step 6) are then brought to bear.
-- source:
--   Unique-source lemma (step 5) of the factor-chain attack plan for the Diophantine remainder of the special-exponent k = 1 case of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)). Follows from multiplicativity of ArithmeticFunction.sigma over coprime prime powers plus the exact-valuation gateway k_one_p_valuation_one.

import Mathlib

namespace OddPerfectNumber

theorem k_one_unique_p_source (p m d : Nat)
    (hp : p.Prime)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hval : padicValNat p (∑ x ∈ (m ^ 2).divisors, x) = 1) :
    ∃! q ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
  sorry

end OddPerfectNumber
