-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_compl_Pl_idem
-- name    : IntMul.Kappa.R8.Bit.Oppbank.compl_Pl_idem
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:58:20.382003+00:00
-- url     : https://prove2.me/theorems/2305d1c0-0065-40be-93f4-0b8daefa63cd
-- title:
--   Complement of densified Pl is idempotent
-- statement:
--   For $b<v$, $(1-\mathrm{Pl}(b))^2=1-\mathrm{Pl}(b)$.
-- source:
--   ex/ei/en K_rank

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem compl_Pl_idem {b : ℕ} (hb : b < v) : (1 - Pl b) * (1 - Pl b) = 1 - Pl b := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
