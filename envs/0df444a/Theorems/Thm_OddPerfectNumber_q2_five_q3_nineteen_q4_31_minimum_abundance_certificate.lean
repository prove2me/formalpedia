-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_minimum_abundance_certificate
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_31_minimum_abundance_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:34:10.884787+00:00
-- url     : https://prove2.me/theorems/b5a22d6f-b1ad-4bc0-b868-43f032022de1
-- title:
--   Minimum abundance certificate for the q4=31 support
-- statement:
--   The minimum even exponents a=6, b=c=e=2 on the support {3,5,19,31} already give divisor-sum abundancy strictly greater than 2, as an exact integer inequality.
-- source:
--   Exact finite arithmetic certificate for the q2=5, q3=19, q4=31 minimum-abundance contradiction. It is independent of the unresolved global branch and is intended as a reusable lower-bound component.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_31_minimum_abundance_certificate :
    2 * (3 ^ 6 * 5 ^ 2 * 19 ^ 2 * 31 ^ 2) <
      (∑ i ∈ Finset.range (6 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 31 ^ i) := by
  sorry

end OddPerfectNumber
