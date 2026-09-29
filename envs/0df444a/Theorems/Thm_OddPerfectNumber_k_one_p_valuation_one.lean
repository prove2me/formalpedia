-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p_valuation_one
-- name    : OddPerfectNumber.k_one_p_valuation_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T07:43:58.903597+00:00
-- url     : https://prove2.me/theorems/a0e4d8fb-2aef-48d9-b360-f7415b2b1aa4
-- title:
--   The k = 1 divisor sum has exact p-adic valuation one
-- statement:
--   Let $p$ be prime with $p \nmid m$ and write $m^2 = t e$ with $t = (p+1)/2$. If the divisor sum satisfies $\sigma(m^2) = p e$, then the exact $p$-adic valuation of $\sigma(m^2)$ is one. Indeed $p \nmid m^2$ (as $p$ is prime), hence $p \nmid e$ (as $e \mid m^2$), so $v_p(p e) = v_p(p) + v_p(e) = 1 + 0$. This is the gateway to step 5 of the factor-chain attack: exactly one local divisor sum $\sigma(q^{2e})$ supplies the single factor $p$.
-- source:
--   Exact-valuation gateway (step 5) of the factor-chain attack plan for the Diophantine remainder of the special-exponent k = 1 case of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)). Uses padicValNat.mul/self/eq_zero_of_not_dvd following the accepted DHP proof patterns.

import Mathlib

namespace OddPerfectNumber

theorem k_one_p_valuation_one (p m e : Nat)
    (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hd : m ^ 2 = ((p + 1) / 2) * e)
    (hsig : (∑ d ∈ (m ^ 2).divisors, d) = p * e) :
    padicValNat p (∑ d ∈ (m ^ 2).divisors, d) = 1 := by
  sorry

end OddPerfectNumber
