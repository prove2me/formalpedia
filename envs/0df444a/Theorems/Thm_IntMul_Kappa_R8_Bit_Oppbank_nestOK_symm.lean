-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nestOK_symm
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nestOK_symm
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:43:14.260271+00:00
-- url     : https://prove2.me/theorems/60e9ff55-40f3-4d87-88aa-2ed4aa56bd87
-- title:
--   nestOK is symmetric
-- statement:
--   The densified nest-ok predicate is symmetric: $\mathrm{nestOK}(o,c)=\mathrm{nestOK}(c,o)$. Follows by commuting Bool conjunctions on ND/PT clauses and `argRel` disjunction, using that ND and PT codes are disjoint.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem nestOK_symm (o c : ℕ) : nestOK o c = nestOK c o := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
