-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_ex
-- name    : IntMul.Kappa.R8.Bit.Oppbank.FB0_ex
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:01:27.789329+00:00
-- url     : https://prove2.me/theorems/0df48954-4e57-437a-a3d9-b713a9198092
-- title:
--   Full flag-basis inhabitance on Lab0 × Pis0 (Dm ∪ Pl)
-- statement:
--   There exist frames $S,S^{-1}$ realising the Defs52 flag-basis property $\mathrm{FB0}$ on densified $\mathrm{Lab0}\times\mathrm{Pis0}$ ($\mathrm{Pis0}=\mathrm{Dm}(\mathrm{idxD})\cup\mathrm{Pl}$).
--
--   The Pl-only fragment $\mathrm{FB0\_ex\_Pl}$ is already proved; this leaf adds densified move idempotents $\mathrm{Dm}$.
-- source:
--   Defs52 FB0; FB0_ex_Pl ACCEPTED 7f4c81df; MoveFacts2 hPis0_of_Dm

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open Matrix
open scoped Kronecker
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem FB0_ex : ∃ S Sinv, FB0 S Sinv := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
