-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO_GoodM_large2
-- name    : IntMul.Kappa.R8.Bit.Oppbank.EOKO_GoodM_large2
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:32:45.548751+00:00
-- url     : https://prove2.me/theorems/70838169-dd40-40b5-9159-7236ea22ff56
-- title:
--   GoodM for EOKO (EOKOPack)
-- statement:
--   # GoodM for densified EOKO (pack)
--
--   Replacement importing `BitOppbankEOKOPack`. Exists $q_0$ with `GoodM` on $S,S^{-1},Pc,Pl$ at large prime powers.
--
--   **Formalization Note.** `EOKO_GoodM_large2`.
-- source:
--   EOKOPack

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem EOKO_GoodM_large2 :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f,
      GoodM (q ^ f) ch0NB.S ∧ GoodM (q ^ f) ch0NB.Si ∧
        (∀ c < SupG.codeBound, GoodM (q ^ f) (Pc c)) ∧
          (∀ b < 1771, GoodM (q ^ f) (Pl b)) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
