-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mPl_mPl_rank_484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_mPl_mPl_rank_484
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:13:15.08267+00:00
-- url     : https://prove2.me/theorems/7bf86ba2-01b6-4c42-a92c-6de5cb19f7de
-- title:
--   Conjugated (1-Pl)⊗(1-Pl) has rank 484
-- statement:
--   For invertible \(S\) and \(a,t<1771\), \(\operatorname{rank}(K(S,S^{-1};1-\mathrm{Pl}_a,1-\mathrm{Pl}_t))=484\). **Formalization Note.** Input to `net0O2_en_PE`.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem K_mPl_mPl_rank_484 (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) {a t : ℕ} (ha : a < 1771) (ht : t < 1771) :
    (K S Si (1 - Pl a) (1 - Pl t)).rank = 484 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
