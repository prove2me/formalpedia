-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_dris_five_reduced_numerator_dvd_two_pow_five
-- name    : OddPerfectNumber.Kernel.dris_five_reduced_numerator_dvd_two_pow_five
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-03T07:32:41.145984+00:00
-- url     : https://prove2.me/theorems/c2caa3e7-762b-4822-936e-009c6fa5af93
-- title:
--   The reduced numerator of the abundancy of the square part divides twice a fifth power
-- statement:
--   Let the two Dris equations hold, so that twice $m$ squared is $\sigma(p^5) s$ and $\sigma(m^2) = p^5 s$. Suppose the divisor sum of $m$ squared factors as $u v$ and $m^2$ factors as $u w$, with $u$ coprime to $w$, as happens when $u$ is the part of $\sigma(m^2)$ coprime to $m^2$. Then $u$ divides $2 p^5 w$.
--
--   The proved theorem `dris_five_sigma_identity` (e2e22704) gives $\sigma(p^5)\sigma(m^2) = 2 p^5 m^2$. Since $u$ divides $\sigma(m^2)$ it follows that $u$ divides $2 p^5 m^2 = 2 p^5 (u w)$, and cancelling the coprime factor $u$ gives the claim.
--
--   In ratio form the same equation says $\sigma(m^2)/m^2 = 2 p^5/\sigma(p^5)$, a prescribed rational strictly between $1$ and $2$. This theorem is the divisibility shadow of that equality after the common factor of numerator and denominator is cancelled, and it is the first consequence of the two Dris equations that mentions neither the square component $d_1^2$ of the index nor its two odd-multiplicity primes. Instantiating $u$, $v$, $w$ with the actual greatest common divisor quotients is a separate and purely arithmetic step.
--
--   Note that the factor $w$ in the conclusion is essential: $u$ is coprime to $w$ but not necessarily to the part of $m^2$ carried by $v$, so the stronger claim that $u$ divides $2 p^5$ is false.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem dris_five_reduced_numerator_dvd_two_pow_five (p m s u v w : Nat)
    (huw : Nat.Coprime u w)
    (hT : (∑ d ∈ (m ^ 2).divisors, d) = u * v)
    (hm2 : m ^ 2 = u * w)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    u ∣ 2 * (p ^ 5 * w) := by
  sorry

end OddPerfectNumber.Kernel
