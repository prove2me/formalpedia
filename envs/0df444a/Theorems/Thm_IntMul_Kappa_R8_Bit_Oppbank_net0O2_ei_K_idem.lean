-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ei_K_idem
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ei_K_idem
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:18:18.419475+00:00
-- url     : https://prove2.me/theorems/a7297ab4-c087-46da-b645-0b08471ec38e
-- title:
--   Idempotence of aux-entrance residual
-- statement:
--   Idempotence of the aux-entrance residual for in-range indices. Feeds `oneRun_of_pivs` / `net0O2_ei_PE`.
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

theorem net0O2_ei_K_idem (a : ℕ) (ha : a < v) :
    K S0 Si0 (1 - Pl a) 1 * K S0 Si0 (1 - Pl a) 1 = K S0 Si0 (1 - Pl a) 1 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
