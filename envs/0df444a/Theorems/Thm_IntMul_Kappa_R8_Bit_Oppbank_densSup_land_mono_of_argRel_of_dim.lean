-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel_of_dim
-- name    : IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRel_of_dim
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:00:43.528904+00:00
-- url     : https://prove2.me/theorems/6726e7ac-8a27-428b-8cc4-a9ccafb4a502
-- title:
--   Dim-strict densSup land-mono on published argRel
-- statement:
--   # Dim-strict bitwise support nesting on published `argRel`
--
--   On the published (non-Fix) packing, `argRel a n` is the disjunction
--   $\mathrm{arg}_0 n=a\lor\mathrm{arg}_1 n=a$ and does not itself contain a
--   dimension test.  Nevertheless, whenever $\mathrm{argRel}\,a\,n$ holds and
--   $\dim F(a)<\dim F(n)$, the bitwise supports nest:
--
--   $$
--   \mathrm{densSupG}(a)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(a).
--   $$
--
--   The argument uses the dim-gated window certificates `LandMonoA0`--`LandMonoA24`
--   (published Pnd, not PndFix) covering every node $n<62478=\mathrm{nNodes}$.
--   This is the published-Pnd analogue of `densSup_land_mono_of_argRelFix`, but it
--   is deliberately dim-strict: the unrestricted claim (no $\dim F$ hypothesis)
--   is not asserted.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: dim-strict densSup_land_mono on published (non-Fix) Pnd.argRel, via LandMonoA0–A24.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
/-- Dim-strict bitwise support nesting on the published (non-Fix) `argRel`. -/
theorem densSup_land_mono_of_argRel_of_dim (a n : ℕ)
    (ha : a < SupG.nNodes) (hn : n < SupG.nNodes)
    (h : argRel a n = true) (hd : dimF a < dimF n) :
    Nat.land (densSupG a) (densSupG n) = densSupG a := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
