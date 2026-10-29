-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_W1F_wires_lt_NL
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_W1F_wires_lt_NL
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:49:04.106302+00:00
-- url     : https://prove2.me/theorems/7092591a-7d51-4401-98dc-91af9889af44
-- title:
--   Local wires of stage-one word W1F lie strictly below NL
-- statement:
--   Every local wire index mentioned by an instruction of the densified stage-one word \(W_{1F}\) is strictly below \(NL=31359\).
--
--   The word \(W_{1F}\) is assembled from LocSlots / GREC accessors (\(w_X,w_Y,w_S,w_T\)) over densified tables. Formally, if \(\ell\) appears in the touch list or as an XOR endpoint of some \(i\in W_{1F}\), then
--   $$
--   \ell < NL.
--   $$
--
--   This is the data-bound leaf of the \(\mathrm{cs1}\) touch densify: combined with \(\mathrm{genF}\) local-preservation it closes \(\mathrm{net0O2\_cs1\_locals\_lt\_NL}\).
--
--   Formalization Note. Bounds follow from layout identities \(w_X(t)=t\), \(w_Y(T)=v+T\), \(w_S(q)=w_{\mathrm{Ent}}+q\), \(w_T(c)=w_{\mathrm{AuxEnd}}+c\) together with LocSlots certificates \(\mathrm{injS},\mathrm{srcS},\mathrm{retS}<NR\) and \(\mathrm{pts}<h\).
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: W1F LocSlots wire bound

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NL)
theorem net0O2_W1F_wires_lt_NL (ℓ : ℕ)
    (hℓ : ∃ i ∈ W1F, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) :
    ℓ < NL := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
