-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_Pl_Pl_rank_one
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_Pl_Pl_rank_one
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:03:07.085993+00:00
-- url     : https://prove2.me/theorems/3e940141-74a7-4882-87cb-06ff90f40bf0
-- title:
--   Conjugated Pl⊗Pl has rank one
-- statement:
--   For invertible \(S\) and labels \(a,s<1771\),
--   \[
--   \operatorname{rank}\bigl(K(S,S^{-1};\mathrm{Pl}_a,\mathrm{Pl}_s)\bigr)=1.
--   \]
--
--   **Formalization Note.** PE leaf input for `net0O2_ec_PE` via OneRunPE2.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem K_Pl_Pl_rank_one (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) {a s : ℕ} (ha : a < 1771) (hs : s < 1771) :
    (K S Si (Pl a) (Pl s)).rank = 1 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
