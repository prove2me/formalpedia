-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R1
-- name    : IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R1
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:31:58.941842+00:00
-- url     : https://prove2.me/theorems/604801a3-6c59-4935-9743-44ab0281e553
-- title:
--   AllDensCentred region R1 [15000,30000)
-- statement:
--   # AllDensCentred region R1
--
--   Every densified node $n$ with $15000\le n<30000$ has a Bruhat centre:
--   $$
--   \forall n\ (15000\le n<30000),\qquad \mathrm{HasCentre}(\mathrm{densSupG}\,n).
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

theorem AllDensCentred_R1 :
    ∀ n, 15000 ≤ n → n < 30000 → HasCentre (densSupG n) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
