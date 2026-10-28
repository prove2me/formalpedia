-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_pos
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_pos
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:34:15.889731+00:00
-- url     : https://prove2.me/theorems/3ee8927c-8f29-4d38-8fb7-ea6cef4e67c1
-- title:
--   Dm idempotent at positive rkC
-- statement:
--   For in-range codes with $r=\mathrm{rkC}(o,c)>0$, $\mathrm{Dm}(o,c)$ is idempotent. Supports `net0O2_e1_K_idem` / `e2_K_idem`.
--
--   **Formalization Note.** Via Pc nesting / `le_sub_idem`; may strengthen with `nestOK`.
-- source:
--   supports e1/e2_K_idem; retry codeBound open

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem Dm_idem_pos (o c : ℕ) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    Dm o c * Dm o c = Dm o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
