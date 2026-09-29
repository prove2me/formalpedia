-- Prove2me | Theorems.Thm_OddPerfectNumber_order_three_mod_601_eq_75
-- name    : OddPerfectNumber.order_three_mod_601_eq_75
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T15:59:21.495132+00:00
-- url     : https://prove2.me/theorems/d862c0d9-43da-44b8-a7ef-aa23e563ed84
-- title:
--   The order of 3 modulo 601 is 75
-- statement:
--   The residue class of 3 modulo 601 has multiplicative order 75.
-- source:
--   Exact finite order certificate for the D=57 q4=601 candidate, using orderOf_eq_iff and exact ZMod arithmetic.

import Mathlib

namespace OddPerfectNumber

theorem order_three_mod_601_eq_75 :
    orderOf (3 : ZMod 601) = 75 := by
  sorry

end OddPerfectNumber
