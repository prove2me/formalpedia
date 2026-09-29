-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_valuation_flow
-- name    : OddPerfectNumber.k_one_valuation_flow
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T06:25:46.506708+00:00
-- url     : https://prove2.me/theorems/88a7cc62-814c-4168-9e21-aab4b701537a
-- title:
--   The k = 1 divisor sums satisfy the valuation-flow identity
-- statement:
--   Let $p$ be prime with $p \equiv 1 \pmod 4$ and $m$ odd with $p \nmid m$, satisfying the bridge equation $(1+p)\sigma(m^2) = 2pm^2$ with $t = (p+1)/2$. Then $\sigma(m^2) = p\prod_q q^{v_q(m^2) - v_q(t)}$, the product over the prime divisors $q$ of $m^2$. Since $t \mid m^2$, every prime divisor of $t$ already divides $m^2$, so with $d = m^2/t$ this is $\sigma(m^2) = pd$ with $d$ factored over the same prime support: writing $m = \prod q_i^{e_i}$ and $a_i = v_{q_i}(t)$ with $0 \le a_i \le 2e_i$, $\prod_i \sigma(q_i^{2e_i}) = p\prod_i q_i^{2e_i - a_i}$. This is the exact directed factor-chain identity (step 4 of the factor-chain attack): every prime divisor of every local divisor sum $\sigma(q_i^{2e_i})$ must lie in $\{p, q_1, \ldots, q_r\}$.
-- source:
--   Valuation-flow identity (step 4) of the factor-chain attack plan for the Diophantine remainder of the special-exponent k = 1 case of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)). Uses ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul for the left side and the deficiency witness for sigma(m^2) = p*d.

import Mathlib

namespace OddPerfectNumber

theorem k_one_valuation_flow (p m : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (heq : (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p * m ^ 2)) :
    (∑ d ∈ (m ^ 2).divisors, d)
      = p * ∏ q ∈ (m ^ 2).primeFactors,
          q ^ ((m ^ 2).factorization q - ((p + 1) / 2).factorization q) := by
  sorry

end OddPerfectNumber
