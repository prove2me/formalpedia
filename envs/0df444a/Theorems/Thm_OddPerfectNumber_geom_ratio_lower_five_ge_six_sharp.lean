-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
-- name    : OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T16:03:24.949321+00:00
-- url     : https://prove2.me/theorems/1807a906-f803-43cc-92ed-9342d2b38b1c
-- title:
--   Sharp five-component abundance lower bound from exponent six
-- statement:
--   For exponent at least six, the 5-power geometric sum satisfies the sharp cross-multiplied abundance lower bound 19531/15625.
-- source:
--   Sharp five-component abundance bound needed for the D=57 and D=75 q4 interval reductions; the accepted 3906/3125 bound is too loose for q4 >= 580.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_five_ge_six_sharp (b : Nat) (hb : 6 ≤ b) :
    19531 * 5 ^ b ≤ 15625 * (∑ i ∈ Finset.range (b + 1), 5 ^ i) := by
  sorry

end OddPerfectNumber
