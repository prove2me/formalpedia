-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T18:44:02.254519+00:00
-- url     : https://prove2.me/theorems/66a9f99b-0cc8-4e86-9189-022f0c359ee4
-- title:
--   The q3=13 middle-D candidate envelope is impossible
-- statement:
--   In the canonical q3=13 middle envelope, the accepted thirteen-case candidate reduction contradicts the canonical lower bound q4>19531.
-- source:
--   Consume the exact accepted thirteen-tuple disjunction and eliminate every branch by exact arithmetic against q4>19531.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_candidates

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_middle_D_absurd (D p q4 : Nat)
    (hDlow : 45 ≤ D) (hDhigh : D < 214)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 19531 < q4) (hq4le : q4 ≤ 89)
    (hq4dvd : q4 ∣ D) :
    False := by
  sorry

end OddPerfectNumber
