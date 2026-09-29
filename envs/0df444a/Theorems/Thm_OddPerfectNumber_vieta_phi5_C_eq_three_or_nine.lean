-- Prove2me | Theorems.Thm_OddPerfectNumber_vieta_phi5_C_eq_three_or_nine
-- name    : OddPerfectNumber.vieta_phi5_C_eq_three_or_nine
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T00:45:34.576456+00:00
-- url     : https://prove2.me/theorems/04e8e8f4-8d33-441e-a696-5182967b8875
-- title:
--   Pure Vieta classification: x^2+x+y^2+y+1 = C(xy-1) forces C = 3 or C = 9
-- statement:
--   Every positive natural solution of x^2+x+y^2+y+1 = C(xy-1) has C = 3 or C = 9. Pure Vieta-jumping classification by strong induction on x+y with the subtraction-free other-root construction; base case x<=3 by the factored difference identity, six numeric pairs checked exactly. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. Independent of OPN hypotheses, primality, order, Phi5 API. Stopping point is C in {3,9}; recurrence components NOT asserted.

import Mathlib

namespace OddPerfectNumber

theorem vieta_phi5_C_eq_three_or_nine (x y C : Nat)
    (hx : 0 < x)
    (hy : 0 < y)
    (heq : x ^ 2 + x + y ^ 2 + y + 1 = C * (x * y - 1)) :
    C = 3 ∨ C = 9 := by
  sorry

end OddPerfectNumber
