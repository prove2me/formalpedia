-- Prove2me | Theorems.Thm_OddPerfectNumber_order_three_mod_587_eq_293
-- name    : OddPerfectNumber.order_three_mod_587_eq_293
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T15:59:21.993244+00:00
-- url     : https://prove2.me/theorems/af27189e-3e9f-4473-a7ea-31ae3f1c0c84
-- title:
--   The order of 3 modulo 587 is 293
-- statement:
--   The residue class of 3 modulo 587 has multiplicative order 293.
-- source:
--   Exact finite order certificate for the D=57 q4=587 candidate, using orderOf_eq_iff and exact ZMod arithmetic.

import Mathlib

namespace OddPerfectNumber

theorem order_three_mod_587_eq_293 :
    orderOf (3 : ZMod 587) = 293 := by
  sorry

end OddPerfectNumber
