-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel_of_dim_R2
-- name    : IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRel_of_dim_R2
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:11:23.606065+00:00
-- url     : https://prove2.me/theorems/2c3a6ce3-819f-477b-8685-5696013b0235
-- title:
--   Dim-gated densSup land certificates on published Pnd, nodes 25000–37499
-- statement:
--   # Dim-gated densSup land certificates on published Pnd, region $R_2$
--
--   For every node $n$ with $25000\le n<37500$ and each argument slot $i\in\{0,1\}$, $\dim F(\mathrm{arg}_i n)<\dim F(n)$ implies $\mathrm{densSupG}(\mathrm{arg}_i n)\mathbin{\&}\mathrm{densSupG}(n)=\mathrm{densSupG}(\mathrm{arg}_i n)$.\n\nThe certificates are on the published (non-Fix) `argF` / `dimF` / `densSupG`. This is an intermediate range lemma for dim-strict `densSup_land_mono_of_argRel_of_dim`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: range consolidator for dim-strict land-mono on published Pnd.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
/-- Dim-gated land for arg0/arg1 on published (non-Fix) Pnd, index region. -/
theorem densSup_land_mono_of_argRel_of_dim_R2 (n : ℕ) (hn0 : 25000 ≤ n) (hn1 : n < 37500) :
    ((!Nat.blt (dimF (Nat.land (argF n) 65535)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.land (argF n) 65535)) (densSupG n))
        (densSupG (Nat.land (argF n) 65535))) = true) ∧
    ((!Nat.blt (dimF (Nat.shiftRight (argF n) 16)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.shiftRight (argF n) 16)) (densSupG n))
        (densSupG (Nat.shiftRight (argF n) 16))) = true) := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
