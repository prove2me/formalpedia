-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion
-- name    : OddPerfectNumber.four_support_factorization_expansion
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T15:54:03.533575+00:00
-- url     : https://prove2.me/theorems/a00d0ec5-6689-48ea-83b1-d6d822ded5af
-- title:
--   Expand a four-prime support factorization
-- statement:
--   A nonzero natural with exactly the four distinct prime-support entries q1,q2,q3,q4 expands as the corresponding product of prime powers.
-- source:
--   Four-support factorization layer for the Odd Perfect Number abundance proof; this is pure unique factorization and does not assert any OPN contradiction.

import Mathlib

namespace OddPerfectNumber

theorem four_support_factorization_expansion (n q1 q2 q3 q4 : Nat)
    (hn : n ≠ 0)
    (hsupport : n.primeFactors = {q1, q2, q3, q4})
    (hne12 : q1 ≠ q2) (hne13 : q1 ≠ q3) (hne14 : q1 ≠ q4)
    (hne23 : q2 ≠ q3) (hne24 : q2 ≠ q4) (hne34 : q3 ≠ q4) :
    n = q1 ^ n.factorization q1 * q2 ^ n.factorization q2 *
      q3 ^ n.factorization q3 * q4 ^ n.factorization q4 := by
  sorry

end OddPerfectNumber
