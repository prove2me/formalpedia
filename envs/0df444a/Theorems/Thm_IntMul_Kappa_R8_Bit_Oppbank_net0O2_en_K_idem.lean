-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_K_idem
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_K_idem
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:18:14.017417+00:00
-- url     : https://prove2.me/theorems/5d6dbbcd-8ee6-422d-8cab-8a57b07203b6
-- title:
--   Idempotence of data residual
-- statement:
--   Idempotence of the data residual for in-range indices. Feeds `oneRun_of_pivs` / `net0O2_en_PE`.
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

theorem net0O2_en_K_idem (a t : ℕ) (ha : a < v) (ht : t < v) :
    K S0 Si0 (1 - Pl a) (1 - Pl t) * K S0 Si0 (1 - Pl a) (1 - Pl t) = K S0 Si0 (1 - Pl a) (1 - Pl t) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
