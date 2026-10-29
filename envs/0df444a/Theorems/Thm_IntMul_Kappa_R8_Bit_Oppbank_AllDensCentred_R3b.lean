-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R3b
-- name    : IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R3b
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:48:42.261438+00:00
-- url     : https://prove2.me/theorems/d910dda8-efb4-4200-ba2f-8e9a43e6636b
-- title:
--   AllDensCentred region R3b [55000,62478)
-- statement:
--   # AllDensCentred region R3b\n\nHasCentre on dens nodes $[55000,62478)$.\n
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

theorem AllDensCentred_R3b :
    ∀ n, 55000 ≤ n → n < 62478 → HasCentre (densSupG n) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
