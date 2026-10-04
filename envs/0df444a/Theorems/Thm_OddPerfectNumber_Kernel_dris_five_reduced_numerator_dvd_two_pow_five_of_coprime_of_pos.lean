-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_dris_five_reduced_numerator_dvd_two_pow_five_of_coprime_of_pos
-- name    : OddPerfectNumber.Kernel.dris_five_reduced_numerator_dvd_two_pow_five_of_coprime_of_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T10:04:08.854711+00:00
-- url     : https://prove2.me/theorems/3527114a-7e42-49c4-bd33-e8d5c21e2459
-- title:
--   The reduced numerator of the forced abundancy divides twice a fifth power
-- statement:
--   Suppose $m$ and $s$ are nonzero and the two Dris equations hold, so that $2 m^2 = \sigma(p^5) s$ and $\sigma(m^2) = p^5 s$. Suppose the divisor sum of $m^2$ factors as $u v$ and $m^2$ factors as $v w$, with $u$ coprime to $w$, as happens when $g = \gcd(\sigma(m^2), m^2)$, $u = \sigma(m^2)/g$, $v = g$ and $w = m^2/g$. Then $u$ divides $2 p^5 w$.
--
--   The proved theorem $\mathtt{dris\_five\_sigma\_identity}$ (e2e22704) gives $\sigma(p^5)\sigma(m^2) = 2 p^5 m^2$. Substituting the two factorisations yields $\sigma(p^5)(u v) = 2 p^5 (v w)$, that is $(\sigma(p^5) u) v = (2 p^5 w) v$. Since $m \neq 0$ the divisor sum is strictly positive, so $u v \neq 0$ and therefore $v \neq 0$; cancelling $v$ gives $\sigma(p^5) u = 2 p^5 w$, and $u$ divides the right-hand side because it divides $\sigma(p^5) u$.
--
--   This is the third statement in this family and corrects two earlier false ones. The first, $\mathtt{dris\_five\_reduced\_numerator\_dvd\_two\_pow\_five}$ (c2caa3e7), required $m^2 = u w$ instead of $m^2 = v w$, which made it false because $u = \gcd(\sigma(m^2), m^2)$ then satisfied its hypotheses. The second, $\mathtt{dris\_five\_reduced\_numerator\_dvd\_two\_pow\_five\_of\_coprime}$ (e7e21834), had the correct factorisation but no non-degeneracy hypothesis, so it is false for every prime $p \neq 3$: take $m = 0$, $s = 0$, $u = 3$, $v = 0$, $w = 1$. All five of its hypotheses hold, since $\sigma(0) = 0$, yet its conclusion $3 \mid 2 p^5$ fails. The present statement adds exactly the missing $m \neq 0$.
--
--   In ratio form the same identity says $\sigma(m^2)/m^2 = 2 p^5/\sigma(p^5)$, a prescribed rational strictly between $1$ and $2$, so this remains the first consequence of the two Dris equations that mentions neither the square component $d_1^2$ of the index nor its two odd-multiplicity primes.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem dris_five_reduced_numerator_dvd_two_pow_five_of_coprime_of_pos (p m s u v w : Nat)
    (hm0 : m != 0) (hs0 : s != 0)
    (huw : Nat.Coprime u w)
    (hT : (∑ d ∈ (m ^ 2).divisors, d) = u * v)
    (hm2 : m ^ 2 = v * w)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    u ∣ 2 * (p ^ 5 * w) := by
  sorry

end OddPerfectNumber.Kernel
