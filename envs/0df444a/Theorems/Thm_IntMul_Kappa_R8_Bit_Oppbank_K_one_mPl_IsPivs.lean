-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_one_mPl_IsPivs
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_one_mPl_IsPivs
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:09:49.468979+00:00
-- url     : https://prove2.me/theorems/354239f5-7b23-4457-bfbf-151174d468ea
-- title:
--   Origin diagonal pivots for 1⊗(1-Pl) under FB0
-- statement:
--   Under \(\mathrm{FB0}(S,S^{-1})\) and \(b<1771\), origin diagonal pivots \(k<22\) for \(K(S,S^{-1};1,1-\mathrm{Pl}_b)\).
--   **Formalization Note.** Closes `net0O2_ex_PE`.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R6.Bit.NB (IsPiv)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem K_one_mPl_IsPivs (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hFB : FB0 S Si) {b : ℕ} (hb : b < 1771) :
    ∀ k, k < 22 → IsPiv (K S Si 1 (1 - Pl b)) k k := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
