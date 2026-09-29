-- Prove2me | Theorems.Thm_OddPerfectNumber_order_37_mod_73_eq_9_v2
-- name    : OddPerfectNumber.order_37_mod_73_eq_9_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T06:53:13.756174+00:00
-- url     : https://prove2.me/theorems/9f8a4566-cf33-4ec7-a6d6-5b13b976f365
-- title:
--   The q3=29 D=37 source order (v2)
-- statement:
--   The multiplicative order of 37 modulo 73 is exactly 9.
-- source:
--   Corrected exact order certificate: a prime divisor of 9 is reduced through 9=3^2 before identifying it with 3.

import Mathlib

namespace OddPerfectNumber

theorem order_37_mod_73_eq_9_v2 : orderOf (37 : ZMod 73) = 9 := by
  sorry

end OddPerfectNumber
