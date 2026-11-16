-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_g1_inj_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.g1_inj_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:26:36.498408+00:00
-- url     : https://prove2.me/theorems/5def9634-701f-412b-bce2-cc15d74cddf0
-- title:
--   The stage-one bank map $g_1$ is injective (QHNetRec)
-- statement:
--   The stage-one local-to-global embedding \(g_1\) is injective on the product of bank indices and local wires, on the total-decoder network `QHNetRec`.
--
--   Fix bank indices \(b,b'<1771\) and local wires \(w,w'<NL=31359\). If \(g_1(b,w)=g_1(b',w')\), then necessarily \(b=b'\) and \(w=w'\):
--
--   $$
--   b,b'<1771,\qquad w,w'<NL,\qquad g_1(b,w)=g_1(b',w')\implies b=b'\land w=w'.
--   $$
--
--   The map \(g_1\) is the four-piece opp-bank layout embedding: a factor of \(v=1771\) on the first two bands (offset by \(N=3136441\) on the second), a slot band of width \(NR=27794\) below \(W=104719230\), and a height-\(h=23\) temporary band above \(W\). Distinct bands occupy disjoint integer intervals, and within each band the representation is unique for these bounds.
--
--   **Formalization Note.** The statement is identical to `g1_inj`, with preamble importing `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec` rather than `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet` (the published `WireLayout` module is reused and does not import the parent QHNet). It does not close or replace `58ea51e9-97c9-4b0a-9a0e-fe732d331728`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: injectivity of g1, restated on the total-decoder fork IntMul_Kappa_R8_Data_BitOppbankQHNetRec (d127abea). Does not close or replace 58ea51e9-97c9-4b0a-9a0e-fe732d331728.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank (g1 NL v)
theorem g1_inj_rec {b b' w w' : ℕ} (hb : b < 1771) (hb' : b' < 1771)
    (hw : w < NL) (hw' : w' < NL) (h : g1 b w = g1 b' w') :
    b = b' ∧ w = w' := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
