-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_pickE_oneRun
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_pickE_oneRun
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:50:40.834329+00:00
-- url     : https://prove2.me/theorems/0397d57f-6c4b-4255-8d63-550d488b28ff
-- title:
--   pickE of inhabited OneRun2 PE returns a oneRun edge
-- statement:
--   If the one-run edge predicate $\mathrm{PE}(q,\mathrm{oneRun}(r))$ is inhabited, then `pickE` returns a witness whose run list realises `oneRun r`. Immediate from the choose-spec of `pickE`.
--
--   **Formalization Note.** Uses OneRunMomExpand `pickE_of_exists`.
-- source:
--   OneRun2; OneRunMomExpand 7fe078b1 pickE_of_exists

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open Matrix

theorem net0O2_pickE_oneRun (r : ℕ) (q : Matrix (Fin 529) (Fin 529) ℚ)
    (h : ∃ e, PE q (oneRun r) e) :
    oneRun r (pickE (PE q (oneRun r))).runs := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
