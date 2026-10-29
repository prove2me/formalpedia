-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_one_mPl_rank_22
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_one_mPl_rank_22
-- status  : Disproved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:09:42.709281+00:00
-- url     : https://prove2.me/theorems/103e2381-5961-4081-a7f7-4c772c436119
-- title:
--   Conjugated 1⊗(1-Pl) has rank 22
-- statement:
--   For invertible \(S\) and \(b<1771\), \(\operatorname{rank}(K(S,S^{-1};1,1-\mathrm{Pl}_b))=22\).
--   **Formalization Note.** Input to `net0O2_ex_PE`.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem K_one_mPl_rank_22 (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) {b : ℕ} (hb : b < 1771) :
    (K S Si 1 (1 - Pl b)).rank = 22 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
