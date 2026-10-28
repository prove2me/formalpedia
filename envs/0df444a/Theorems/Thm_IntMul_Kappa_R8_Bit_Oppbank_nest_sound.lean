-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_sound
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nest_sound
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:45:25.111965+00:00
-- url     : https://prove2.me/theorems/e0baa6ba-ce7c-49af-9069-d5e3a5d3cf3d
-- title:
--   Densified nestOK implies Le orientation of Pc
-- statement:
--   If $\mathrm{nestOK}(o,c)$ holds for densified codes $o,c<\mathrm{codeBound}$, then the projectors are nested: $\mathrm{Le}(\mathrm{Pc}\,o,\mathrm{Pc}\,c)$ or the reverse. Port of R6 `nest_sound` to densified supports.
-- source:
--   R6 nest_sound in sol_bitNetR6_mom; R8 densified Pnd nestOK

import Definitions.Def_IntMul_Kappa_R6_Defs4
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

theorem nest_sound {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : nestOK o c = true) :
    Le (Pc o) (Pc c) ∨ Le (Pc c) (Pc o) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
