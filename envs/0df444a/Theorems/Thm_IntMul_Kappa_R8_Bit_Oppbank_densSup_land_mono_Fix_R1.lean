-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_Fix_R1
-- name    : IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_Fix_R1
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:45:18.650335+00:00
-- url     : https://prove2.me/theorems/d0e304e0-1b94-4ae6-be2f-df835bce35e7
-- title:
--   Dim-gated densSup land mono region R1 [12500,25000)
-- statement:
--   # Dim-gated densSup land region R1
--
--   For densified indices $n$ with $12500\le n<25000$, both packed arguments satisfy the dim-gated land implication. Supports `densSup_land_mono_of_argRelFix`.
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
/-- Dim-gated land for arg0/arg1 on n ∈ [12500,25000). -/
theorem densSup_land_mono_Fix_R1 (n : ℕ) (hn0 : 12500 ≤ n) (hn1 : n < 25000) :
    ((!Nat.blt (dimF (Nat.land (argF n) 65535)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.land (argF n) 65535)) (densSupG n))
        (densSupG (Nat.land (argF n) 65535))) = true) ∧
    ((!Nat.blt (dimF (Nat.shiftRight (argF n) 16)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (Nat.shiftRight (argF n) 16)) (densSupG n))
        (densSupG (Nat.shiftRight (argF n) 16))) = true) := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
