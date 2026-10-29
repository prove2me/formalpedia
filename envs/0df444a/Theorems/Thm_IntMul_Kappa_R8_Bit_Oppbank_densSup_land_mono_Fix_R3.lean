-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_Fix_R3
-- name    : IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_Fix_R3
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:45:11.175046+00:00
-- url     : https://prove2.me/theorems/6f67ebcf-5c85-4131-98de-e7eff193125e
-- title:
--   Dim-gated densSup land mono region R3 [37500,50000)
-- statement:
--   # Dim-gated densSup land region R3
--
--   For densified indices $n$ with $37500\le n<50000$, both packed arguments satisfy the dim-gated land implication. Supports `densSup_land_mono_of_argRelFix`.
-- source:
--   R8 BitOppbank PndFix land mono

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndFix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
/-- Dim-gated land for arg0/arg1 on n ∈ [37500,50000). -/
theorem densSup_land_mono_Fix_R3 (n : ℕ) (hn0 : 37500 ≤ n) (hn1 : n < 50000) :
    ((!Nat.blt (dimF (Nat.land (argF n) 65535)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.land (argF n) 65535)) (densSupG n))
        (densSupG (Nat.land (argF n) 65535))) = true) ∧
    ((!Nat.blt (dimF (Nat.shiftRight (argF n) 16)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.shiftRight (argF n) 16)) (densSupG n))
        (densSupG (Nat.shiftRight (argF n) 16))) = true) := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
