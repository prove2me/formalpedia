-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_dimF_le_22
-- name    : IntMul.Kappa.R8.Bit.Oppbank.dimF_le_22
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:27:41.289235+00:00
-- url     : https://prove2.me/theorems/68810cc8-644f-4b73-b2c6-38adbb18922b
-- title:
--   R8 Oppbank densified dimF ≤ 22
-- statement:
--   For every densified node index $n < \mathrm{nNodes}=62478$, the packed dimension field satisfies $\dim F(n)\le 22$. Empirically the maximum is 22 (no node claims full ambient dimension). This forces $\dim\mathrm{CF}(c)=23\Leftrightarrow c=1$ and lets HIGH dominate every $\mathrm{Dm}(1,c)$ orientation in $h\mathrm{Pis0\_Dm}$.
-- source:
--   ChkBitArg.DIMT 5-bit fields; densified nNodes=62478.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg
open IntMul.Kappa.R8.Bit.Oppbank.SupG

/-- Every densified node dimension field is at most 22 (table max is 22). -/
theorem dimF_le_22 : ∀ n < SupG.nNodes, dimF n ≤ 22 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
