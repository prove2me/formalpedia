-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred
-- name    : IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:54:39.031893+00:00
-- url     : https://prove2.me/theorems/39987973-45cf-4516-9a44-dae4ccfb0b31
-- title:
--   Every densified node support has a centre
-- statement:
--   Every densified JF-stack node $n<\mathrm{nNodes}$ has a Bruhat centre certificate:
--   $$\forall n<\mathrm{nNodes},\qquad \mathrm{HasCentre}(\mathrm{densSupG}(n)).$$
--   This unlocks honest ND projectors $\mathrm{Pc}(1773+n)=\mathrm{Pnd}(\mathrm{densSupG}\,n)$ for nest Le.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem AllDensCentred :
    ∀ n < SupG.nNodes, HasCentre (densSupG n) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
