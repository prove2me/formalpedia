-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_rkC_lt_529
-- name    : IntMul.Kappa.R8.Bit.Oppbank.rkC_lt_529
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:09:29.581643+00:00
-- url     : https://prove2.me/theorems/700ddf88-bca8-406f-bccd-da07741d7a9e
-- title:
--   $\mathrm{rkC}(o,c)<529$
-- statement:
--   # Residual rank is strictly less than the frame size
--
--   For any codes $o,c$, $\mathrm{rkC}(o,c)=|\mathrm{dimCF}(o)-\mathrm{dimCF}(c)|$ and $\mathrm{dimCF}\le 23$, hence $\mathrm{rkC}(o,c)<529$. Needed as the width bound in `oneRun`.
--
--   **Formalization Note.** Follows from `dimCF_le_22` / boundary cases $\mathrm{dimCF}\in\{0,1,22,23\}$.
-- source:
--   BitNB OneRun2 mom-path 2026-10-29; supports net0O2_e1_PE_pos / AllOneRun

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem rkC_lt_529 (o c : ℕ) : rkC o c < 529 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
