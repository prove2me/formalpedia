-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_special_exponent_five_s_ge_two
-- name    : OddPerfectNumber.no_dris_special_exponent_five_s_ge_two
-- status  : Open
-- author  : @WillR
-- created : 2026-09-08T22:10:45.971978+00:00
-- url     : https://prove2.me/theorems/98530697-b601-455d-8ca9-48823257a540
-- title:
--   No Dris-index solution for the Euler equation with special exponent $k = 5$ and $s \ge 2$
-- statement:
--   Let $p$ be an odd prime with $p \equiv 1 \pmod 4$, let $m$ be odd with $p \nmid m$, and let $s \ge 2$ be a natural number. The Euler equation for an odd perfect number in Euler form with special exponent $k = 5$ has no Dris-index solution: the two relations $2m^2 = \sigma(p^5)s$ and $\sigma(m^2) = p^5s$ cannot both hold. This is the nontrivial $s \ge 2$ case left after the case $s = 1$ is ruled out by the proved lemma $\sigma(p^5) \ne 2m^2$ since $6 \mid 5 + 1$.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation); Euler form and special-exponent case k = 5 as recorded on the Odd Perfect Number Conjecture mission.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_special_exponent_five_s_ge_two (p m s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs : 2 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  sorry

end OddPerfectNumber
