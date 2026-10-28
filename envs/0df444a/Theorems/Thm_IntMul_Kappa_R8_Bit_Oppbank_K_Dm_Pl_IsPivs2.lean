-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_Dm_Pl_IsPivs2
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_Dm_Pl_IsPivs2
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:22:26.183769+00:00
-- url     : https://prove2.me/theorems/6ddb1e2c-4072-43ae-accb-f42856841c60
-- title:
--   Origin pivots for K(Dm,Pl) under FB0+nestOK
-- statement:
--   Under FB0 and nestOK, origin diagonal pivots for \(K(\mathrm{Dm},\mathrm{Pl})\).

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
open IntMul.Kappa.R6.Bit.NB (IsPiv)
theorem K_Dm_Pl_IsPivs2 (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hFB : FB0 S Si)
    {b o c : ℕ} (hb : b < 1771) (ho : o < codeBound) (hc : c < codeBound)
    (hn : nestOK o c = true) :
    ∀ k, k < rkC o c → IsPiv (K S Si (Dm o c) (Pl b)) k k := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
