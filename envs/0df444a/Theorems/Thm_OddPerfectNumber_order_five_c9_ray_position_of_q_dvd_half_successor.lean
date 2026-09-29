-- Prove2me | Theorems.Thm_OddPerfectNumber_order_five_c9_ray_position_of_q_dvd_half_successor
-- name    : OddPerfectNumber.order_five_c9_ray_position_of_q_dvd_half_successor
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T14:01:58.223729+00:00
-- url     : https://prove2.me/theorems/36e9b0ca-9019-45b8-af77-6ccad50250d9
-- title:
--   Order-five Branch-I C=9 pairs sit at parity-compatible ray positions
-- statement:
--   In the order-five Branch-I context, write p + 1 = q k. Then the C = 9 ray position of the pair (q, k) is one of exactly two parity-compatible shapes: either the Euler-oriented right-ray edge (q, k) = (R(3m), R(3m+1)), or the mirrored left-ray edge q = L(3m+3), k = L(3m+2). The two other parity-compatible orientations are impossible modulo 5 because they force 5 | p with orderOf(q mod p) = 5.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md, formalised through the accepted C=9 ray coverage theorem, the parity period theorems and the mod-five period theorems. The published statement records both surviving ray positions; the journal's single (1,2)-ray conclusion needs the mirrored left-ray orientation excluded separately.

import Mathlib
import Definitions.Def_opnRightRay
import Definitions.Def_opnLeftRay
import Theorems.Thm_OddPerfectNumber_vieta_phi5_C_nine_ray_coverage
import Theorems.Thm_OddPerfectNumber_opnRightRay_parity_period_three
import Theorems.Thm_OddPerfectNumber_opnLeftRay_parity_period_three
import Theorems.Thm_OddPerfectNumber_opnRightRay_mod_five_period_three
import Theorems.Thm_OddPerfectNumber_opnLeftRay_mod_five_period_three
import Theorems.Thm_OddPerfectNumber_opnLeftRay_order_five_euler_impossible
import Theorems.Thm_OddPerfectNumber_order_five_vieta_C_eq_nine_of_q_dvd_half_successor

namespace OddPerfectNumber

theorem order_five_c9_ray_position_of_q_dvd_half_successor (p q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hsqP : IsSquare (p : ZMod q))
    (hqt : q ∣ (p + 1) / 2)
    (h5 : orderOf (q : ZMod p) = 5) :
    ∃ k : Nat,
      p + 1 = q * k ∧
        ((∃ m : Nat, q = opnRightRay (3 * m) ∧ k = opnRightRay (3 * m + 1)) ∨
         (∃ m : Nat, q = opnLeftRay (3 * m + 3) ∧ k = opnLeftRay (3 * m + 2))) := by
  sorry

end OddPerfectNumber
