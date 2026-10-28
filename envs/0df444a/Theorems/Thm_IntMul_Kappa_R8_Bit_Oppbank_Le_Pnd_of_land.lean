-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Le_Pnd_of_land
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Le_Pnd_of_land
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:53:08.491029+00:00
-- url     : https://prove2.me/theorems/17f46ed4-2d47-4acf-84b7-fd4deeeeeb9a
-- title:
--   Bitwise support nesting ⇒ Le Pnd
-- statement:
--   If supports satisfy $s_a\mathbin{\&}s_b=s_a$ and both have centres, the corresponding Bruhat projectors nest:
--   $$\mathrm{Le}(\mathrm{Pnd}(s_a),\mathrm{Pnd}(s_b)).$$
--   Follows from $\mathrm{spanS}(s_a)\le\mathrm{spanS}(s_b)$ and the orthogonal projection characterization.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2

/-- Bitwise support nesting + centres ⇒ Le of Pnd projectors. -/
theorem Le_Pnd_of_land {sa sb : ℕ}
    (hCsa : HasCentre sa) (hCsb : HasCentre sb)
    (h : Nat.land sa sb = sa) :
    Le (Pnd sa) (Pnd sb) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
