-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_Dm_Pl_idem2
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_Dm_Pl_idem2
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:22:01.586324+00:00
-- url     : https://prove2.me/theorems/fc1c4065-c0aa-448c-903f-940ade673faa
-- title:
--   K(Dm,Pl) idempotent under nestOK
-- statement:
--   If \(S\) is invertible and \(\mathrm{nestOK}\,o\,c\), then \(K(S,S^{-1};\mathrm{Dm}\,o\,c,\mathrm{Pl}_b)\) is idempotent.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)
theorem K_Dm_Pl_idem2 (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1)
    {b o c : ℕ} (hb : b < 1771) (ho : o < codeBound) (hc : c < codeBound)
    (hn : nestOK o c = true) :
    K S Si (Dm o c) (Pl b) * K S Si (Dm o c) (Pl b) = K S Si (Dm o c) (Pl b) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
