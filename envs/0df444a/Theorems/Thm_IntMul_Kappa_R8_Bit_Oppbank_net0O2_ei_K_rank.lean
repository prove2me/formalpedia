-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ei_K_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ei_K_rank
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:18:01.175049+00:00
-- url     : https://prove2.me/theorems/1207759e-166a-473c-964c-a324b776df6d
-- title:
--   Rank of aux-entrance residual is 22
-- statement:
--   $\mathrm{rank}$ of the aux-entrance residual equals $22$.
--
--   **Formalization Note.** For `oneRun_of_pivs` width match.
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

theorem net0O2_ei_K_rank (a : ℕ) (ha : a < v) :
    (K S0 Si0 (1 - Pl a) 1).rank = 22 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
