-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_g1_inj
-- name    : IntMul.Kappa.R8.Bit.Oppbank.g1_inj
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:59:24.403044+00:00
-- url     : https://prove2.me/theorems/58ea51e9-97c9-4b0a-9a0e-fe732d331728
-- title:
--   Stage-one global wire map g1 is injective on banks
-- statement:
--   If $b,b'<1771$ and $w,w'<\mathrm{NL}$ satisfy $g_1(b,w)=g_1(b',w')$, then $b=b'$ and $w=w'$.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank (g1 NL v)
theorem g1_inj {b b' w w' : ℕ} (hb : b < 1771) (hb' : b' < 1771)
    (hw : w < NL) (hw' : w' < NL) (h : g1 b w = g1 b' w') :
    b = b' ∧ w = w' := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
