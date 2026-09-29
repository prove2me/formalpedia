-- Prove2me | Theorems.Thm_OddPerfectNumber_vieta_phi5_other_root
-- name    : OddPerfectNumber.vieta_phi5_other_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T00:45:00.205444+00:00
-- url     : https://prove2.me/theorems/8dc0711c-38fd-4827-9a2c-4c2b791266a8
-- title:
--   Vieta move for x^2+x+y^2+y+1 = C(xy-1) preserves positivity and the equation
-- statement:
--   For positive naturals x,y with x^2+x+y^2+y+1 = C(xy-1), the Vieta conjugate z = Cx-(y+1) is positive, satisfies y+z+1 = Cx and yz = x^2+x+C+1, and (x,z) satisfies the same equation. Subtraction-free Nat formulation of the Vieta involution for the Phi5 quotient. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Section 21 Vieta-jumping setup of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. Helper for the pure C in {3,9} classification. No OPN hypotheses, no primality, no order.

import Mathlib

namespace OddPerfectNumber

theorem vieta_phi5_other_root (x y C : Nat)
    (hx : 0 < x)
    (hy : 0 < y)
    (heq : x ^ 2 + x + y ^ 2 + y + 1 = C * (x * y - 1)) :
    ∃ z : Nat, 0 < z ∧ y + z + 1 = C * x ∧ y * z = x ^ 2 + x + C + 1 ∧ x ^ 2 + x + z ^ 2 + z + 1 = C * (x * z - 1) := by
  sorry

end OddPerfectNumber
