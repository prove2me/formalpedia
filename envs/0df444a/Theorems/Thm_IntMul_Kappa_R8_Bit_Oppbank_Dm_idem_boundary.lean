-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_boundary
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_boundary
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:32:29.921786+00:00
-- url     : https://prove2.me/theorems/2f59f0b0-d767-4da1-8c79-d6c440eba45e
-- title:
--   R8 Oppbank Dm idempotent on LOW/HIGH nest boundary
-- statement:
--   If densified codes $o,c < \mathrm{codeBound}$ have $o\le 1$ or $c\le 1$, then $\mathrm{Dm}(o,c)^2=\mathrm{Dm}(o,c)$.
-- source:
--   MoveFacts4/5; dimF_le_22.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem Dm_idem_boundary :
    ∀ o c, o < SupG.codeBound → c < SupG.codeBound →
      o ≤ 1 ∨ c ≤ 1 → Dm o c * Dm o c = Dm o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
