-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_PE_pos
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_e1_PE_pos
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:05:46.591907+00:00
-- url     : https://prove2.me/theorems/b593ed64-f57b-4e7c-8913-a11b3974e39c
-- title:
--   OneRun2 e1 PE at positive rkC
-- statement:
--   Corrected e1 PE with 0 < rkC. Replaces disproved net0O2_e1_PE.
-- source:
--   replaces disproved net0O2_e1_PE 84fa24bb

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem net0O2_e1_PE_pos (b o c : ℕ) (hb : b < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (Dm o c) (Pl b)) (oneRun (rkC o c)) e := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
