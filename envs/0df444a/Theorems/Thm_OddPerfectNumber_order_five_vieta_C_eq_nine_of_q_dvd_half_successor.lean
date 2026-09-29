-- Prove2me | Theorems.Thm_OddPerfectNumber_order_five_vieta_C_eq_nine_of_q_dvd_half_successor
-- name    : OddPerfectNumber.order_five_vieta_C_eq_nine_of_q_dvd_half_successor
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T08:33:55.722625+00:00
-- url     : https://prove2.me/theorems/dcd68ab1-dac9-48a7-8d80-07dc389b6ff3
-- title:
--   Order-five Branch-I Vieta quotient has C = 9
-- statement:
--   In the order-five Branch-I context, if p is prime with p = 1 mod 4, q is prime, q divides (p+1)/2, p is a square modulo q, and orderOf(q mod p) = 5, then the exact Nat Vieta quotient exists and its coefficient is C = 9. This composes the accepted order-five quotient, pure Vieta classification C in {3,9}, Branch-I congruence q = 1 mod 4, and direct mod-4 exclusion of C = 3.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. Source-faithful composition of accepted Prove2Me children 58563e74-b832-462a-a20c-9ea6a6d1cc52, 04e8e8f4-8d33-441e-a696-5182967b8875, 0142d099-42f4-4900-90a5-ecaf8ee071e8, and 49f2dc29-4035-4716-a2d5-c09b428916d2. No decomposition edge is changed.

import Mathlib

namespace OddPerfectNumber

theorem order_five_vieta_C_eq_nine_of_q_dvd_half_successor (p q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hsqP : IsSquare (p : ZMod q))
    (hqt : q ∣ (p + 1) / 2)
    (h5 : orderOf (q : ZMod p) = 5) :
    ∃ k C : Nat,
      p + 1 = q * k
      ∧ q ^ 2 + q + k ^ 2 + k + 1 = C * (q * k - 1)
      ∧ C = 9 := by
  sorry

end OddPerfectNumber
