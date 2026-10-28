-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_PTnd
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND_PTnd
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:05:42.885803+00:00
-- url     : https://prove2.me/theorems/66554296-a271-4e54-99f8-7e06231c051b
-- title:
--   PT–ND nestOK + dim order ⇒ Le Pc
-- statement:
--   If densified code $o$ is PT and $c$ is ND, nest-ok, and $\mathrm{dimCF}\,o\le\mathrm{dimCF}\,c$, then
--
--   $$\mathrm{Le}(\mathrm{Pc}\,o,\mathrm{Pc}\,c).$$
--
--   Symmetric $\mathrm{orthOK}$ nesting of $1-\mathrm{Pl}$ under the densified node projector.
-- source:
--   R8 densified PT-ND half of nest_Le_ND

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

theorem nest_Le_ND_PTnd :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      isPT o = true → isND c = true → dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
