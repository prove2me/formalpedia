-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_dris_five_reduced_numerator_dvd_two_pow_five_of_coprime
-- name    : OddPerfectNumber.Kernel.dris_five_reduced_numerator_dvd_two_pow_five_of_coprime
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-03T09:22:03.972518+00:00
-- url     : https://prove2.me/theorems/e7e21834-b20e-435f-9dd9-72326729dcd4
-- title:
--   The reduced numerator of the abundancy of the square part divides twice a fifth power
-- statement:
--   Let the two Dris equations hold, so that twice $m$ squared is $\sigma(p^5) s$ and $\sigma(m^2) = p^5 s$. Suppose the divisor sum of $m$ squared factors as $u v$ and $m^2$ factors as $v w$, with $u$ coprime to $w$, as happens when $g = \gcd(\sigma(m^2), m^2)$, $u = \sigma(m^2)/g$, $v = g$ and $w = m^2/g$. Then $u$ divides $2 p^5 w$.
--
--   The proved theorem $\mathtt{dris\_five\_sigma\_identity}$ (e2e22704) gives $\sigma(p^5)\sigma(m^2) = 2 p^5 m^2$. Substituting the two factorisations yields $\sigma(p^5)(u v) = 2 p^5 (v w)$, and cancelling the shared factor $v$ gives $\sigma(p^5) u = 2 p^5 w$, which is the claim.
--
--   This corrects an earlier statement, $\mathtt{dris\_five\_reduced\_numerator\_dvd\_two\_pow\_five}$ (c2caa3e7), which required $m^2 = u w$ instead of $m^2 = v w$. Under that hypothesis the choice $u = \gcd(\sigma(m^2), m^2)$ satisfies every hypothesis while the conclusion fails, so the earlier statement is false and is not a usable dependency. The coprimality belongs between the two REDUCED quotients $u$ and $w$, which share no factor precisely because the common factor $v$ has been divided out of both.
--
--   In ratio form the same equation says $\sigma(m^2)/m^2 = 2 p^5/\sigma(p^5)$, a prescribed rational strictly between $1$ and $2$, so this is the first consequence of the two Dris equations that mentions neither the square component $d_1^2$ of the index nor its two odd-multiplicity primes.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem dris_five_reduced_numerator_dvd_two_pow_five_of_coprime (p m s u v w : Nat)
    (huw : Nat.Coprime u w)
    (hT : (∑ d ∈ (m ^ 2).divisors, d) = u * v)
    (hm2 : m ^ 2 = v * w)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    u ∣ 2 * (p ^ 5 * w) := by
  sorry

end OddPerfectNumber.Kernel
