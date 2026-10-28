-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_of_Le
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_of_Le
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:26.687988+00:00
-- url     : https://prove2.me/theorems/5f85da9b-6c3d-4f15-8f3c-8e749c763449
-- title:
--   Le orientation of Pc implies Dm idempotent
-- statement:
--   If densified projectors satisfy $\mathrm{Le}(\mathrm{Pc}\,o,\mathrm{Pc}\,c)$ or the reverse, then $\mathrm{Dm}(o,c)$ is idempotent (using $\mathrm{Pc}$ idempotence and $\mathrm{le\_sub\_idem}$, with the equal-rank corner when the dimension comparison opposes the nesting).
-- source:
--   R6 move_facts / le_sub_idem; R8 MoveFacts3

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

theorem Dm_idem_of_Le {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : Le (Pc o) (Pc c) ∨ Le (Pc c) (Pc o)) :
    Dm o c * Dm o c = Dm o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
