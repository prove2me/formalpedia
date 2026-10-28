-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mPl_mPl_IsPivs
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_mPl_mPl_IsPivs
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:13:21.225881+00:00
-- url     : https://prove2.me/theorems/5a64a986-2047-4dfd-a522-4e06eacfabc0
-- title:
--   Origin diagonal pivots for (1-Pl)⊗(1-Pl) under FB0
-- statement:
--   Under \(\mathrm{FB0}(S,S^{-1})\) and \(a,t<1771\), origin diagonal pivots \(k<484\) for \(K(S,S^{-1};1-\mathrm{Pl}_a,1-\mathrm{Pl}_t)\). **Formalization Note.** Closes `net0O2_en_PE`.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R6.Bit.NB (IsPiv)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem K_mPl_mPl_IsPivs (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hFB : FB0 S Si) {a t : ℕ} (ha : a < 1771) (ht : t < 1771) :
    ∀ k, k < 484 → IsPiv (K S Si (1 - Pl a) (1 - Pl t)) k k := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
