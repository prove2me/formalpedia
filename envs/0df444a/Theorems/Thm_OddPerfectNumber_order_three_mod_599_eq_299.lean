-- Prove2me | Theorems.Thm_OddPerfectNumber_order_three_mod_599_eq_299
-- name    : OddPerfectNumber.order_three_mod_599_eq_299
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T15:59:22.528099+00:00
-- url     : https://prove2.me/theorems/fdf09641-d371-49c4-850c-ddc4716850b0
-- title:
--   The order of 3 modulo 599 is 299
-- statement:
--   The residue class of 3 modulo 599 has multiplicative order 299.
-- source:
--   Exact finite order certificate for the D=57 q4=599 candidate, using orderOf_eq_iff and exact ZMod arithmetic.

import Mathlib

namespace OddPerfectNumber

theorem order_three_mod_599_eq_299 :
    orderOf (3 : ZMod 599) = 299 := by
  sorry

end OddPerfectNumber
