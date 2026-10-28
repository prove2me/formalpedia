-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_Dm_Pl_rank2
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_Dm_Pl_rank2
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:22:32.248979+00:00
-- url     : https://prove2.me/theorems/5c394321-9656-45b2-962b-4cb0ef73eabc
-- title:
--   rank K(Dm,Pl) = rkC under nestOK
-- statement:
--   Under invertible \(S\) and nestOK, rank of \(K(\mathrm{Dm},\mathrm{Pl})\) equals \(\mathrm{rkC}\).

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
theorem K_Dm_Pl_rank2 (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1)
    {b o c : ℕ} (hb : b < 1771) (ho : o < codeBound) (hc : c < codeBound)
    (hn : nestOK o c = true) :
    (K S Si (Dm o c) (Pl b)).rank = rkC o c := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
