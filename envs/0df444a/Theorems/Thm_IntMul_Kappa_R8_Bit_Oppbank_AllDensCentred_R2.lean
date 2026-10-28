-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R2
-- name    : IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R2
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:33:52.462298+00:00
-- url     : https://prove2.me/theorems/e63d84c3-eb17-458b-874a-eb9c96b118c5
-- title:
--   AllDensCentred region R2 [30000,45000)
-- statement:
--   # AllDensCentred region R2
--
--   Every densified node $n$ with $30000\le n<45000$ has a Bruhat centre:
--   $$
--   \forall n\ (30000\le n<45000),\qquad \mathrm{HasCentre}(\mathrm{densSupG}\,n).
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

theorem AllDensCentred_R2 :
    ∀ n, 30000 ≤ n → n < 45000 → HasCentre (densSupG n) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
