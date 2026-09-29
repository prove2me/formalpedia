-- Prove2me | Theorems.Thm_OddPerfectNumber_split_prime_part
-- name    : OddPerfectNumber.split_prime_part
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T08:55:05.019835+00:00
-- url     : https://prove2.me/theorems/49c42783-acd7-4ea6-a47f-17230462cc59
-- title:
--   Splitting off the full prime-power part of a divisor
-- statement:
--   Let $q$ be prime dividing a nonzero $m$. Then $m$ splits as $m = q^a w$ with $a \ge 1$ and $q \nmid w$: take $a$ to be the exact multiplicity and $w$ the complementary cofactor. This prime-part splitting is the standard opening move of every valuation-flow argument about divisor sums: it isolates the full $q$-power dividing $m$ so that multiplicativity of $\sigma$ separates the local factor $\sigma(q^{2a})$ from the coprime remainder. Extracted (with gratitude) from the local toolkit of the accepted proof of the $s = 3$ Dris case at special exponent $k = 5$.
-- source:
--   Local DHP toolkit of the accepted Prove2Me proof of OddPerfectNumber.no_dris_five_s_odd_eq_three (Sylvester-contradiction architecture); Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem split_prime_part (q m : Nat) (hq : q.Prime) (hm : m ≠ 0)
    (hqm : q ∣ m) : ∃ a w, 1 ≤ a ∧ m = q ^ a * w ∧ ¬ q ∣ w := by
  sorry

end OddPerfectNumber
