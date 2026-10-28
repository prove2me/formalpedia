-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e2_K_idem
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_e2_K_idem
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:14:27.542489+00:00
-- url     : https://prove2.me/theorems/078b04bc-c193-46fb-8cb4-15132c7f2db7
-- title:
--   Idempotence of e2 residual
-- statement:
--   Idempotence of the stage-two densified residual $K(S_0,S_i,\mathrm{Pl}(a),\mathrm{Dm}(o,c))$ for in-range codes with positive $\mathrm{rkC}$. Required by `oneRun_of_pivs` for `net0O2_e2_PE_pos`.
--
--   **Formalization Note.** Retry after publish-host DB flake on Defs7 import.
-- source:
--   supports net0O2_e2_PE_pos; retry

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_e2_K_idem (a o c : ℕ) (ha : a < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    K S0 Si0 (Pl a) (Dm o c) * K S0 Si0 (Pl a) (Dm o c) = K S0 Si0 (Pl a) (Dm o c) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
