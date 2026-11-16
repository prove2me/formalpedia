-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_gw_inj_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.gw_inj_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:26:44.990971+00:00
-- url     : https://prove2.me/theorems/94a83f00-8e6c-43fe-bbb4-512b5f322f9b
-- title:
--   The global decoder $g_w$ is injective below $W+T_{\mathrm{mp}}$ (QHNetRec)
-- statement:
--   The global-wire decoder \(g_w\) of the total-decoder network `QHNetRec` is injective on the half-open interval \([0,W+T_{\mathrm{mp}})\).
--
--   The decoder sends a natural number \(g\) to the left summand \(\mathrm{inl}\,g\) when \(g<W=104719230\), and otherwise to the right summand \(\mathrm{inr}\,((g-W)\bmod T_{\mathrm{mp}})\) with \(T_{\mathrm{mp}}=3217907\). Consequently, if \(g,g'<W+T_{\mathrm{mp}}\) and \(g_w(g)=g_w(g')\), then \(g=g'\):
--
--   $$
--   g,g'<W+T_{\mathrm{mp}},\qquad g_w(g)=g_w(g')\implies g=g'.
--   $$
--
--   The two summands are disjoint, and on the temporary band the hypothesis \(g<W+T_{\mathrm{mp}}\) removes the modulus, so the preimage is unique.
--
--   **Formalization Note.** The statement is identical to `gw_inj`, with preamble importing `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec` rather than `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`. The constant \(g_w\) lives in the `NB` namespace of `QHNetRec`. It does not close or replace `caa6d350-2a07-447d-8a36-7b5a86f5e00e`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: injectivity of gw, restated on the total-decoder fork IntMul_Kappa_R8_Data_BitOppbankQHNetRec (d127abea). Does not close or replace caa6d350-2a07-447d-8a36-7b5a86f5e00e.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB (gw)
open IntMul.Kappa.R8.Bit.Oppbank (W Tmp)
theorem gw_inj_rec {g g' : ℕ} (hg : g < W + Tmp) (hg' : g' < W + Tmp)
    (h : gw g = gw g') : g = g' := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
