-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pl_rank_one
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Pl_rank_one
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:52:50.053219+00:00
-- url     : https://prove2.me/theorems/4c5b22c9-5a2f-49c9-b3f8-b326fa8dbc02
-- title:
--   Densified Pl has rank 1
-- statement:
--   For $T<v$, $\operatorname{rank}(\mathrm{Pl}(T))=1$ (line projector $x_T y_T^\top$ with $y_T\cdot x_T=1$).
-- source:
--   K_rank calculus

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem Pl_rank_one {b : ℕ} (hb : b < v) : (Pl b).rank = 1 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
