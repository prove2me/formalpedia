-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_of_argRel
-- name    : IntMul.Kappa.R8.Bit.Oppbank.densSup_land_of_argRel
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:53:14.517827+00:00
-- url     : https://prove2.me/theorems/d767e3de-12bb-41bd-a699-7d49ba87c617
-- title:
--   argRel ⇒ densSupG bitwise nesting
-- statement:
--   If $\mathrm{argRel}(a,n)$, the densified supports are bitwise nested: one of
--   $$\mathrm{densSupG}(a)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(a)$$
--   or the reverse holds. This is the combinatorial content of JF-stack argument links used for projector nesting.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem densSup_land_of_argRel (a n : ℕ)
    (ha : a < SupG.nNodes) (hn : n < SupG.nNodes)
    (h : argRel a n = true) :
    Nat.land (densSupG a) (densSupG n) = densSupG a ∨
      Nat.land (densSupG n) (densSupG a) = densSupG n := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
