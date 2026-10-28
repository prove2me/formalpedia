-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Pc_rank
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:12:14.581843+00:00
-- url     : https://prove2.me/theorems/a13098fc-b662-4760-9d1b-ce9a128877ba
-- title:
--   Rank of densified Pc equals dimCF
-- statement:
--   For every densified code $c<codeBound$,
--
--   $$\mathrm{rank}(\mathrm{Pc}\,c)=\mathrm{dimCF}\,c.$$
--
--   LOW/HIGH/PT are elementary; ND uses $\mathrm{Pnd\_rank}=\mathrm{finrank}\,\mathrm{spanS}$ together with the densified dimension table.
-- source:
--   R6 Pc_rank; densified DimBound/Pnd_rank

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem Pc_rank {c : ℕ} (hc : c < codeBound) : (Pc c).rank = dimCF c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
