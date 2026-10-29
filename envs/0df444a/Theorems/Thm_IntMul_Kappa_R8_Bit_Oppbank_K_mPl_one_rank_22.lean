-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mPl_one_rank_22
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_mPl_one_rank_22
-- status  : Disproved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:09:41.737002+00:00
-- url     : https://prove2.me/theorems/9b287df4-8403-4a49-9df3-c1d1b2bac398
-- title:
--   Conjugated (1-Pl)⊗1 has rank 22
-- statement:
--   For invertible \(S\) and \(a<1771\),
--   \[\operatorname{rank}(K(S,S^{-1};1-\mathrm{Pl}_a,1))=22.\]
--   **Formalization Note.** Input to `net0O2_ei_PE`.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem K_mPl_one_rank_22 (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) {a : ℕ} (ha : a < 1771) :
    (K S Si (1 - Pl a) 1).rank = 22 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
