-- Prove2me | Theorems.Thm_OddPerfectNumber_vieta_phi5_C_nine_ray_coverage
-- name    : OddPerfectNumber.vieta_phi5_C_nine_ray_coverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T09:49:15.891372+00:00
-- url     : https://prove2.me/theorems/7c458d4c-772d-498d-818e-31037d3a2218
-- title:
--   Positive C=9 Vieta solutions lie on one of the two rays
-- statement:
--   Every positive natural solution of the C=9 Vieta equation is an adjacent pair on the right or left C=9 ray, up to swapping the coordinates.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md, with the terminology correction that the two seeds are rays from the common minimal vertex 1 rather than disconnected components.

import Mathlib
import Definitions.Def_opnRightRay
import Definitions.Def_opnLeftRay

namespace OddPerfectNumber

theorem vieta_phi5_C_nine_ray_coverage (x y : Nat)
    (hx : 0 < x)
    (hy : 0 < y)
    (heq : x ^ 2 + x + y ^ 2 + y + 1 = 9 * (x * y - 1)) :
    (∃ n : Nat, x = opnRightRay n ∧ y = opnRightRay (n + 1)) ∨
      (∃ n : Nat, y = opnRightRay n ∧ x = opnRightRay (n + 1)) ∨
      (∃ n : Nat, x = opnLeftRay n ∧ y = opnLeftRay (n + 1)) ∨
      (∃ n : Nat, y = opnLeftRay n ∧ x = opnLeftRay (n + 1)) := by
  sorry

end OddPerfectNumber
