-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_rank_eq_rkC
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Dm_rank_eq_rkC
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:51:57.880533+00:00
-- url     : https://prove2.me/theorems/4bf43d34-deb1-4d69-b570-58c8b4ca5f0f
-- title:
--   Rank of Dm equals rkC when positive
-- statement:
--   For $o,c<\mathrm{codeBound}$ with $\mathrm{rkC}(o,c)>0$, $\operatorname{rank}(\mathrm{Dm}(o,c))=\mathrm{rkC}(o,c)$ (difference of nested projectors).
-- source:
--   K_rank calculus

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem Dm_rank_eq_rkC {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) : (Dm o c).rank = rkC o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
