-- Prove2me | Theorems.Thm_OddPerfectNumber_even_order_31_mod_61
-- name    : OddPerfectNumber.even_order_31_mod_61
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T12:07:55.959211+00:00
-- url     : https://prove2.me/theorems/97d35761-b3fe-4a26-a26a-f2f76bee0720
-- title:
--   Even multiplicative order of 31 modulo 61
-- statement:
--   The multiplicative order of 31 modulo 61 is even.
-- source:
--   Use 61-1=4*15. A hypothetical odd order divides 15, which would force 31^15=1; decide verifies that residue is not 1.

import Mathlib

namespace OddPerfectNumber

theorem even_order_31_mod_61 : Even (orderOf (31 : ZMod 61)) := by
  sorry

end OddPerfectNumber
