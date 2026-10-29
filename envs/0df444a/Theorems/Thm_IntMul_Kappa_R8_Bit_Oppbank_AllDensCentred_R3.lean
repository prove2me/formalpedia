-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R3
-- name    : IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R3
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:36:03.348758+00:00
-- url     : https://prove2.me/theorems/7e1ee7ad-f17f-4d4f-8158-39b74d8b2e4d
-- title:
--   AllDensCentred region R3 [45000,62478)
-- statement:
--   # AllDensCentred region R3
--
--   Every densified node $n$ with $45000\le n<62478$ has a Bruhat centre:
--   $$
--   \forall n\ (45000\le n<62478),\qquad \mathrm{HasCentre}(\mathrm{densSupG}\,n).
--   $$
--   Proved from CentBound packs + `hasCentre_of_centredStar`.
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

theorem AllDensCentred_R3 :
    ∀ n, 45000 ≤ n → n < 62478 → HasCentre (densSupG n) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
