-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_g1_lt_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.g1_lt_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:26:33.272964+00:00
-- url     : https://prove2.me/theorems/4f90e46b-3a1b-4c97-9805-e3c28aec57cc
-- title:
--   The stage-one bank map $g_1$ lands below $W+T_{\mathrm{mp}}$ (QHNetRec)
-- statement:
--   The stage-one local-to-global embedding \(g_1\) lands strictly below the global wire bound \(W+T_{\mathrm{mp}}\), on the total-decoder network `QHNetRec`.
--
--   Fix a bank index \(b<1771\) and a local wire \(w<NL=31359\). Then
--
--   $$
--   g_1(b,w) < W + T_{\mathrm{mp}},
--   $$
--
--   where \(W=104719230\) is the permanent-role count and \(T_{\mathrm{mp}}=3217907\) is the temporary-band width. In particular every value of \(g_1\) is a legitimate argument of the decoder \(g_w\), which sends integers below \(W\) to the left summand and the remainder, reduced modulo \(T_{\mathrm{mp}}\), to the right summand.
--
--   **Formalization Note.** The statement is identical to `g1_lt`, with preamble importing `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec` rather than `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet` (the published `WireLayout` module is reused and does not import the parent QHNet). It does not close or replace `d0bd646e-61eb-400a-9343-a22dccdc56c2`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: range bound for g1, restated on the total-decoder fork IntMul_Kappa_R8_Data_BitOppbankQHNetRec (d127abea). Does not close or replace d0bd646e-61eb-400a-9343-a22dccdc56c2.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank (g1 NL W Tmp)
theorem g1_lt_rec {b w : ℕ} (hb : b < 1771) (hw : w < NL) : g1 b w < W + Tmp := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
