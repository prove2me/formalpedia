-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pickE_PE_of_channel
-- name    : IntMul.Kappa.R8.Bit.Oppbank.pickE_PE_of_channel
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:01:39.535985+00:00
-- url     : https://prove2.me/theorems/b0170535-881c-46d9-9b83-81b3256d1643
-- title:
--   Channel pickE is inhabited one-run PE when not default
-- statement:
--   # Non-default channel pickE is inhabited
--
--   If a channel edge equals \(\mathrm{pickE}(\mathrm{PE}(q,\mathrm{oneRun}\,r))\) and is not \(\mathrm{dfltE}\), then \(\mathrm{PE}(q,\mathrm{oneRun}\,r)\) is inhabited and the edge equals that pickE.
--
--   Supports \`edges_as_pickE\` from \`edges_channel_pickE\`.
-- source:
--   edges_as_pickE support

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open Matrix

theorem pickE_PE_of_channel (q : Matrix (Fin 529) (Fin 529) ℚ) (r : ℕ)
    (e : Edge 529) (he : e = pickE (PE q (oneRun r))) (hne : e ≠ dfltE) :
    (∃ e', PE q (oneRun r) e') ∧ e = pickE (PE q (oneRun r)) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
