-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R3a
-- name    : IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R3a
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:46:48.484694+00:00
-- url     : https://prove2.me/theorems/47620b0f-4ea0-4d90-ab23-1cad8f8acd0d
-- title:
--   AllDensCentred region R3a [45000,55000)
-- statement:
--   # AllDensCentred region R3a\n\nHasCentre on dens nodes $[45000,55000)$.\n
-- source:
--   R8 BitOppbank AllDensCentred split

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem AllDensCentred_R3a :
    ∀ n, 45000 ≤ n → n < 55000 → HasCentre (densSupG n) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
