-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_g1_lt
-- name    : IntMul.Kappa.R8.Bit.Oppbank.g1_lt
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:59:32.858607+00:00
-- url     : https://prove2.me/theorems/d0bd646e-61eb-400a-9343-a22dccdc56c2
-- title:
--   Stage-one g1 lands below W+Tmp
-- statement:
--   For $b<1771$ and $w<\mathrm{NL}$, one has $g_1(b,w)<W+\mathrm{Tmp}$.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank (g1 NL W Tmp)
theorem g1_lt {b w : ℕ} (hb : b < 1771) (hw : w < NL) : g1 b w < W + Tmp := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
