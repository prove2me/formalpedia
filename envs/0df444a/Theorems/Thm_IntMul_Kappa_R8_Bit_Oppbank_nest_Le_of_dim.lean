-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_of_dim
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nest_Le_of_dim
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:47:50.574285+00:00
-- url     : https://prove2.me/theorems/fcc1a032-5d88-45ba-b7e2-ded775c96f22
-- title:
--   Nest-ok + dim order ⇒ Le (Pc o)(Pc c)
-- statement:
--   When densified codes $(o,c)$ are nest-ok and $\mathrm{dimCF}(o)\le\mathrm{dimCF}(c)$, the corresponding projectors are nested:
--
--   $$\mathrm{Le}(\mathrm{Pc}(o),\mathrm{Pc}(c)).$$
--
--   This is the dim-directed half of nest-soundness used to prove interior $\mathrm{Dm}$ idempotence via `le_sub_idem`.

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

theorem nest_Le_of_dim :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
