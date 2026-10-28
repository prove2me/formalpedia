-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_K_idem
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ex_K_idem
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:18:40.070984+00:00
-- url     : https://prove2.me/theorems/064aadfc-e0a4-48b5-b969-ab6c14831925
-- title:
--   Idempotence of aux-exit residual
-- statement:
--   Idempotence of the aux-exit residual for in-range indices. Feeds `oneRun_of_pivs` / `net0O2_ex_PE`.
--
--   **Formalization Note.** Pair of ec/e1 K_idem children.
-- source:
--   OneRunPE2 fixed-width PE children 2026-10-29

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_ex_K_idem (b : ℕ) (hb : b < v) :
    K S0 Si0 1 (1 - Pl b) * K S0 Si0 1 (1 - Pl b) = K S0 Si0 1 (1 - Pl b) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
