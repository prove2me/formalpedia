-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_ND
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND_ND
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:05:44.863718+00:00
-- url     : https://prove2.me/theorems/5f6ad737-c65d-4a5d-b6e4-5cd2d626d22f
-- title:
--   ND–ND nestOK + dim order ⇒ Le Pc
-- statement:
--   If densified codes $o,c$ are both ND (endpoints $>1$), nest-ok, and $\mathrm{dimCF}\,o\le\mathrm{dimCF}\,c$, then $\mathrm{Le}(\mathrm{Pc}\,o,\mathrm{Pc}\,c)$. Follows from densified support nesting under $\mathrm{argRel}$ plus $\mathrm{Le\_Pnd\_of\_land}$.
-- source:
--   R8 densified ND-ND half of nest_Le_ND

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem nest_Le_ND_ND :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      isND o = true → isND c = true → dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
