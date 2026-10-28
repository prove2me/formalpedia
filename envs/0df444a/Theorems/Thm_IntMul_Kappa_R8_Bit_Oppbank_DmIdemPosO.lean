-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_DmIdemPosO
-- name    : IntMul.Kappa.R8.Bit.Oppbank.DmIdemPosO
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:16:42.517602+00:00
-- url     : https://prove2.me/theorems/edec8833-ca83-4d65-b27e-ba5ff4c269e0
-- title:
--   Dm idempotent for positive origin codes
-- statement:
--   For densified codes with $o\neq 0$ and $\mathrm{nestOK}(o,c)$,
--
--   $$\mathrm{Dm}(o,c)^2=\mathrm{Dm}(o,c).$$
--
--   Together with MoveFacts4 $\mathrm{Dm\_idem\_o0}$ this yields $\mathrm{hPis0\_Dm}$.
-- source:
--   R6 move_facts/nest_sound; MoveFacts3/4

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem DmIdemPosO :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      o ≠ 0 → Dm o c * Dm o c = Dm o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
