-- Prove2me | Theorems.Thm_OddPerfectNumber_opnLeftRay_parity_period_three
-- name    : OddPerfectNumber.opnLeftRay_parity_period_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T09:31:27.956432+00:00
-- url     : https://prove2.me/theorems/e1f33006-3524-4868-92f6-0d3476327ea6
-- title:
--   Left C=9 ray parity period three
-- statement:
--   The left C=9 ray has odd, even, even parity on every consecutive block of three terms.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. The left ray values 1,6,52,461,... have parity pattern odd, even, even with period three.

import Mathlib
import Definitions.Def_opnLeftRay

namespace OddPerfectNumber

theorem opnLeftRay_parity_period_three (m : Nat) :
    Odd (opnLeftRay (3 * m)) ∧
      Even (opnLeftRay (3 * m + 1)) ∧
      Even (opnLeftRay (3 * m + 2)) := by
  sorry

end OddPerfectNumber
