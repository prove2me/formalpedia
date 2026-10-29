-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_compl_Pl_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.compl_Pl_rank
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:57:20.346984+00:00
-- url     : https://prove2.me/theorems/d06a66a6-421c-43ea-9c96-53d4f17d5f6b
-- title:
--   Complement of densified Pl has rank 22
-- statement:
--   For $b<v$, $\operatorname{rank}(1-\mathrm{Pl}(b))=22$.
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

theorem compl_Pl_rank {b : ℕ} (hb : b < v) : (1 - Pl b).rank = 22 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
