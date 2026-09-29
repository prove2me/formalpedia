-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_not_even
-- name    : OddPerfectNumber.no_dris_thirteen_s_ge_two_not_even
-- status  : Open
-- author  : @WillR
-- created : 2026-09-11T06:12:56.071987+00:00
-- url     : https://prove2.me/theorems/4322828e-04cf-4a19-936a-69f83b71d8ad
-- title:
--   Dris-index case s ge 2 with s not even is impossible for k >= 13
-- statement:
--   Let $p$ be an odd prime with $p \equiv 1 \pmod 4$, let $k \equiv 1 \pmod 4$ with $k \ge 13$, let $m$ be odd with $p \nmid m$, and let $s \ge 2$ with $s$ not even. Then the two Dris relations $2m^2 = \sigma(p^k)s$ and $\sigma(m^2) = p^ks$ cannot both hold. This is the odd-$s$ half of the $s \ge 2$ Dris problem for special exponent $k \ge 13$, left after the even-$s$ half is ruled out by the $2$-adic obstruction.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation); Euler form and special-exponent case k >= 13 as recorded on the Odd Perfect Number Conjecture mission.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_thirteen_s_ge_two_not_even (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
