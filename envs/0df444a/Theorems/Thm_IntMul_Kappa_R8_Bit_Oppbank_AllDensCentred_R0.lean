-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R0
-- name    : IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R0
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:30:10.557905+00:00
-- url     : https://prove2.me/theorems/455f4537-ab03-4f01-9a3e-6239c5d68e2f
-- title:
--   AllDensCentred region R0 [0,15000)
-- statement:
--   # AllDensCentred region R0
--
--   Every densified node $n$ with $0\le n<15000$ has a Bruhat centre:
--   $$
--   \forall n\ (0\le n<15000),\qquad \mathrm{HasCentre}(\mathrm{densSupG}\,n).
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

theorem AllDensCentred_R0 :
    ∀ n < 15000, HasCentre (densSupG n) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
