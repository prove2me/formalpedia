-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_interior
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_interior
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:32:52.539542+00:00
-- url     : https://prove2.me/theorems/b2902db7-7eb8-4a44-9959-47ecfd704322
-- title:
--   R8 Oppbank Dm idempotent on interior nests
-- statement:
--   If densified codes $o,c < \mathrm{codeBound}$ satisfy $\mathrm{nestOK}(o,c)$ with both $>1$, then $\mathrm{Dm}(o,c)^2=\mathrm{Dm}(o,c)$.
-- source:
--   Pnd.nestOK/Dm.

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

theorem Dm_idem_interior :
    ∀ o c, o < SupG.codeBound → c < SupG.codeBound → nestOK o c = true →
      ¬ o ≤ 1 → ¬ c ≤ 1 → Dm o c * Dm o c = Dm o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
