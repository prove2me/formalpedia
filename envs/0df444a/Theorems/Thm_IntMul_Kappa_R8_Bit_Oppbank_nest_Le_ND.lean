-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:56:14.719665+00:00
-- url     : https://prove2.me/theorems/c32724d0-bffa-46be-a387-c29c721a1b2a
-- title:
--   Interior nest Le (endpoints > 1)
-- statement:
--   For nest-ok codes with both endpoints outside $\{0,1\}$ and $\mathrm{dimCF}(o)\le\mathrm{dimCF}(c)$,
--   $$\mathrm{Le}(\mathrm{Pc}(o),\mathrm{Pc}(c)).$$
--   Covers ND–ND `argRel` and ND–PT `orthOK`; uses densSup bitwise nesting and `Le_Pnd_of_land`.

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

theorem nest_Le_ND :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      ¬ o ≤ 1 → ¬ c ≤ 1 → dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
