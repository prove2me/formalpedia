-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_NDpt
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND_NDpt
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:05:30.127274+00:00
-- url     : https://prove2.me/theorems/6f07ed1f-d286-4a86-a8d8-821893a3c71c
-- title:
--   ND–PT nestOK + dim order ⇒ Le Pc
-- statement:
--   If densified code $o$ is ND and $c$ is PT, nest-ok, and $\mathrm{dimCF}\,o\le\mathrm{dimCF}\,c$, then
--
--   $$\mathrm{Le}(\mathrm{Pc}\,o,\mathrm{Pc}\,c).$$
--
--   Uses densified $\mathrm{orthOK}$ to place the node projector under the complementary triple projector $1-\mathrm{Pl}$.
-- source:
--   R8 densified ND-PT half of nest_Le_ND

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

theorem nest_Le_ND_NDpt :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      isND o = true → isPT c = true → dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
