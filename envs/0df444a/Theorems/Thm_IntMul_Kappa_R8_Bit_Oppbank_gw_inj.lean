-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_gw_inj
-- name    : IntMul.Kappa.R8.Bit.Oppbank.gw_inj
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:59:17.124441+00:00
-- url     : https://prove2.me/theorems/caa6d350-2a07-447d-8a36-7b5a86f5e00e
-- title:
--   Global wire embedding gw is injective below W+Tmp
-- statement:
--   If $g,g'<W+\mathrm{Tmp}$ and $\mathrm{gw}\,g=\mathrm{gw}\,g'$, then $g=g'$.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB (gw)
open IntMul.Kappa.R8.Bit.Oppbank (W Tmp)
theorem gw_inj {g g' : ℕ} (hg : g < W + Tmp) (hg' : g' < W + Tmp)
    (h : gw g = gw g') : g = g' := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
