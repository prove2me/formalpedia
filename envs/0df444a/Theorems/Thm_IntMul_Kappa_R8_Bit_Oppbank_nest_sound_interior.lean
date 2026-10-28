-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_sound_interior
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nest_sound_interior
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:54:49.362827+00:00
-- url     : https://prove2.me/theorems/6a1cc324-5bf9-466a-9e50-82c6fb77b240
-- title:
--   Interior nestOK implies Pc nesting (either orientation)
-- statement:
--   For densified codes with $o,c>1$ and $\mathrm{nestOK}(o,c)$, the projectors are nested in one orientation:
--   $$\mathrm{Le}(\mathrm{Pc}\,o,\mathrm{Pc}\,c)\lor\mathrm{Le}(\mathrm{Pc}\,c,\mathrm{Pc}\,o).$$
--   This is the interior half of R6 `nest_sound` (ND–ND via `argRel`, ND–PT via `orthOK`).
-- source:
--   R6 nest_sound; R8 densified Pc/Pnd

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

theorem nest_sound_interior :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      ¬ o ≤ 1 → ¬ c ≤ 1 →
      Le (Pc o) (Pc c) ∨ Le (Pc c) (Pc o) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
