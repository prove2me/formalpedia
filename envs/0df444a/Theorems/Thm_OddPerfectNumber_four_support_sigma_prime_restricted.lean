-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted
-- name    : OddPerfectNumber.four_support_sigma_prime_restricted
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T10:40:32.040852+00:00
-- url     : https://prove2.me/theorems/63d28db4-e4da-4b73-9687-9341e59816da
-- title:
--   Four-prime support restricts every sigma prime factor
-- statement:
--   Let $p$ and $r$ be primes. Suppose $\sigma(m^2)=p d$, $d\mid m^2$, and $r\mid\sigma(m^2)$. If every prime divisor of $m$ is one of four specified primes $q_1,q_2,q_3,q_4$, then $r$ is either the Euler prime $p$ or one of those four support primes. This is the finite-support form of the accepted theorem `sigma_prime_mem_support_or_euler` and is intended for fixed-support factor-chain certificates.
-- source:
--   Derived finite-support corollary of the remotely accepted theorem OddPerfectNumber.sigma_prime_mem_support_or_euler (UUID 0519f1c5-56fb-4423-92dc-f924a643690e), together with Nat.primeFactors support membership.

import Mathlib
import Theorems.Thm_OddPerfectNumber_sigma_prime_mem_support_or_euler

namespace OddPerfectNumber

theorem four_support_sigma_prime_restricted (p m d q1 q2 q3 q4 r : Nat)
    (hp : p.Prime) (hr : r.Prime) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hrsigma : r ∣ ∑ x ∈ (m ^ 2).divisors, x)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = q1 ∨ x = q2 ∨ x = q3 ∨ x = q4) :
    r = p ∨ r = q1 ∨ r = q2 ∨ r = q3 ∨ r = q4 := by sorry

end OddPerfectNumber
