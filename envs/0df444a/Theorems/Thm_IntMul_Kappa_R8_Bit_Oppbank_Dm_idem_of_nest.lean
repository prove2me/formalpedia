-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_of_nest
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_of_nest
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:46:50.27865+00:00
-- url     : https://prove2.me/theorems/afad0690-95e5-4aa5-9aff-6eac934aa9e6
-- title:
--   nestOK implies densified Dm idempotent
-- statement:
--   For densified codes $o,c<\mathrm{codeBound}$ with $\mathrm{nestOK}(o,c)$, the move projector is idempotent: $\mathrm{Dm}(o,c)^2=\mathrm{Dm}(o,c)$. Follows from densified $\mathrm{nest\_sound}$ plus $\mathrm{Pc}$ idempotence and $\mathrm{le\_sub\_idem}$.
-- source:
--   R6 move_facts; R8 MoveFacts3 Dm_idem_le/ge + nest_sound

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

theorem Dm_idem_of_nest {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : nestOK o c = true) : Dm o c * Dm o c = Dm o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
