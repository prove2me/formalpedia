-- Prove2me | Theorems.Thm_OddPerfectNumber_opnRightRay_mod_five_period_three
-- name    : OddPerfectNumber.opnRightRay_mod_five_period_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T09:31:45.947419+00:00
-- url     : https://prove2.me/theorems/dc113c00-8da3-4f06-9f0f-fa8a1a3fab07
-- title:
--   Right C=9 ray mod five period three
-- statement:
--   The right C=9 ray has residues 1,2,1 modulo five on every consecutive block of three terms.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. The right ray values modulo five repeat 1,2,1.

import Mathlib
import Definitions.Def_opnRightRay

namespace OddPerfectNumber

theorem opnRightRay_mod_five_period_three (m : Nat) :
    opnRightRay (3 * m) % 5 = 1 ∧
      opnRightRay (3 * m + 1) % 5 = 2 ∧
      opnRightRay (3 * m + 2) % 5 = 1 := by
  sorry

end OddPerfectNumber
