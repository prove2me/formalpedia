-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_PE
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ex_PE
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:48:05.501989+00:00
-- url     : https://prove2.me/theorems/7d67d9b5-9358-4803-8ef9-03dcaa46d2bb
-- title:
--   OneRun2 exit PE width 22
-- statement:
--   Exit edges of width 22. **Formalization Note.** Qualified `OneRunNet2.PE`.
-- source:
--   OneRun2 e0d447f6; OneRunPE2 b8f301c1; track BitNB 2026-10-29

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem net0O2_ex_PE (b : ℕ) (hb : b < v) :
    ∃ e, OneRunNet2.PE (K S0 Si0 1 (1 - Pl b)) (oneRun 22) e := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
