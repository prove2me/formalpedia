-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_rank_PT
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_PT
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:16:06.386893+00:00
-- url     : https://prove2.me/theorems/af74be6b-4f08-432b-8439-79034f576ddf
-- title:
--   PT code: rank (1-Pl)=22
-- statement:
--   For PT codes $2\le c<1773$, $\mathrm{Pc}\,c=1-\mathrm{Pl}(c-2)$ has rank $22=\mathrm{dimCF}\,c$.
-- source:
--   R6 pt_facts rank

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
theorem Pc_rank_PT {c : ℕ} (h2 : 2 ≤ c) (hPT : c < 1773) :
    (Pc c).rank = 22 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
