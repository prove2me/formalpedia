-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nestOK_of_rkC_pos
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nestOK_of_rkC_pos
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:51:34.00562+00:00
-- url     : https://prove2.me/theorems/446b8e74-d1b5-44ac-a049-29d8986227a8
-- title:
--   Positive rkC implies densified nestOK
-- statement:
--   # Positive dim-gap forces nestOK
--
--   For codes $o,c<\mathrm{codeBound}$, if $\mathrm{rkC}(o,c)>0$ then $\mathrm{nestOK}(o,c)=\mathrm{true}$.
--
--   **Formalization Note.** Bridge for `Dm_idem_pos`. May be false in full generality — if so, strengthen `Dm_idem_pos` with an explicit nest hypothesis instead.
-- source:
--   Dm_idem_pos bridge

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem nestOK_of_rkC_pos {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) : nestOK o c = true := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
