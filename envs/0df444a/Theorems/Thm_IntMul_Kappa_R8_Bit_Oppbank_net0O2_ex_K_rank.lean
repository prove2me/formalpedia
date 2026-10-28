-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_K_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ex_K_rank
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:19:55.807253+00:00
-- url     : https://prove2.me/theorems/abdfd5ef-532b-4499-af19-5c6f30a8a2e5
-- title:
--   Rank of aux-exit residual is 22
-- statement:
--   $\mathrm{rank}\,K(S_0,S_i,1,1-\mathrm{Pl}(b))=22$ for $b<v$. Retry after publish DB flake.
--
--   **Formalization Note.** Width for `oneRun 22` / `net0O2_ex_PE`.
-- source:
--   retry ex_K_rank

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_ex_K_rank (b : ℕ) (hb : b < v) :
    (K S0 Si0 1 (1 - Pl b)).rank = 22 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
