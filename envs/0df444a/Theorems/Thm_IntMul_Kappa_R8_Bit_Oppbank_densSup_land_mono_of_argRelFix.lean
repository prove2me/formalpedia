-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRelFix
-- name    : IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRelFix
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:08:44.260478+00:00
-- url     : https://prove2.me/theorems/e0645568-009d-44dc-9488-08b2b23be434
-- title:
--   argRelFix ⇒ directed densSupG nesting
-- statement:
--   # Directed densSup nesting under dimension-strict $\mathrm{argRel}$
--
--   Using `BitOppbankPndFix` (dim-strict $\mathrm{argRel}$), if $\mathrm{argRel}(a,n)$ and $a,n<nNodes$, then
--   $$
--   \mathrm{densSupG}(a)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(a).
--   $$
--   Replacement for deprecated `densSup_land_mono_of_argRel` (false under published non-strict `argRel` after densify).
-- source:
--   R8 BitOppbank PndFix densify

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

/-- Directed densSup nesting under dim-strict argRel (PndFix). -/
theorem densSup_land_mono_of_argRelFix (a n : ℕ)
    (ha : a < SupG.nNodes) (hn : n < SupG.nNodes)
    (h : argRel a n = true) :
    Nat.land (densSupG a) (densSupG n) = densSupG a := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
