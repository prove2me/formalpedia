-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_dimCF_of_ND
-- name    : IntMul.Kappa.R8.Bit.Oppbank.dimCF_of_ND
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:26:51.904358+00:00
-- url     : https://prove2.me/theorems/c193e9ff-bd38-4ab4-9f13-c3a5da1a4d1f
-- title:
--   dimCF of an ND code is dimF of the underlying node
-- statement:
--   # $\mathrm{dimCF}$ on ND codes
--
--   For every densified node $n$ with $1773+n$ strictly below $\mathrm{codeBound}=64251$,
--   $$\mathrm{dimCF}(1773+n)=\mathrm{dimF}(n).$$
--
--   This is the unfolding of $\mathrm{dimCF}$ on the ND branch (codes $\ge 1773$): the $c=0$, $c=1$, and point-code $(c<1773)$ cases are excluded by the arithmetic of $1773+n$.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: dimCF↔dimF on ND codes, for dim-strict nest_Le.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
/-- On an ND code, `dimCF` is the node dimension `dimF`. -/
theorem dimCF_of_ND {n : ℕ} (hn : 1773 + n < codeBound) :
    dimCF (1773 + n) = dimF n := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
