-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel
-- name    : IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRel
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:06:23.183641+00:00
-- url     : https://prove2.me/theorems/2750f967-01dc-441b-8f5e-8d44d542a17c
-- title:
--   argRel ⇒ directed densSupG nesting
-- statement:
--   If densified nodes satisfy $\mathrm{argRel}(a,n)$, the argument support nests under the result:
--
--   $$\mathrm{densSupG}(a)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(a).$$
--
--   This is the densified port of R6 `argRel_sound` / gate-nesting, used to orient $\mathrm{Le}(\mathrm{Pc}\,(1773+a),\mathrm{Pc}\,(1773+n))$.
-- source:
--   R6 argRel_sound directed; densified ARGT/DAG

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem densSup_land_mono_of_argRel (a n : ℕ)
    (ha : a < SupG.nNodes) (hn : n < SupG.nNodes)
    (h : argRel a n = true) :
    Nat.land (densSupG a) (densSupG n) = densSupG a := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
