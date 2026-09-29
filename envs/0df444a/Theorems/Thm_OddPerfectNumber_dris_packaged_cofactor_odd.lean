-- Prove2me | Theorems.Thm_OddPerfectNumber_dris_packaged_cofactor_odd
-- name    : OddPerfectNumber.dris_packaged_cofactor_odd
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T19:17:54.924331+00:00
-- url     : https://prove2.me/theorems/a2e77f98-78ce-4d31-b1b0-929019cd381e
-- title:
--   Parity bridge: the cofactor $m$ of the packaged Euler configuration is odd
-- statement:
--   Euler's form of a hypothetical odd perfect number $N = p^k m^2$ is frequently packaged into the three identities
--
--   $$\sigma(p^k) = 2t, \qquad m^2 = t\,d, \qquad \sigma(m^2) = p^k d,$$
--
--   together with the Euler congruences $p \equiv k \equiv 1 \pmod 4$. Many statements about this configuration also carry the hypothesis that the cofactor $m$ is odd. This theorem says that this hypothesis is redundant: as soon as $m \neq 0$, the three identities and the two congruences already force $m$ to be odd.
--
--   The argument is $2$-adic. The divisor sum of a nonzero perfect square is always odd (for an even square the $2$-part contributes $2^{2a+1}-1$, and every odd prime contributes a sum of an odd number of odd terms). Since $p \equiv 1 \pmod 4$ we have $\sigma(p^k) \equiv k+1 \equiv 2 \pmod 4$, so $t$ is odd. Multiplying the last two identities gives $\sigma(m^2)\,t = p^k m^2$, whose left-hand side is a product of two odd numbers; as $p$ is odd, the right-hand side can be odd only if $m$ is odd.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (packaging of the Euler equation); Euler (1849) congruences p = k = 1 (mod 4).

import Mathlib
open Finset

namespace OddPerfectNumber

theorem dris_packaged_cofactor_odd (p k m t d : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (p ^ k).divisors, x) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * d) :
    Odd m := by
  sorry

end OddPerfectNumber
