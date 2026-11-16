-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_W1F_wires_lt_NL_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_W1F_wires_lt_NL_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:52:03.079466+00:00
-- url     : https://prove2.me/theorems/5baf9cfc-9fa3-46fb-883f-51ff98bc5ae5
-- title:
--   Local wires of stage-one word W1F lie strictly below NL (QHNetRec)
-- statement:
--   Every local wire index mentioned by an instruction of the densified stage-one word $W_{1F}$ on the total-decoder network `QHNetRec` is strictly below $NL=31359$.
--
--   The word $W_{1F}$ is assembled from LocSlots / GREC accessors ($w_X,w_Y,w_S,w_T$) over densified tables. Formally, if $\ell$ appears in the touch list or as an XOR endpoint of some $i\in W_{1F}$, then
--
--   $$
--   \ell < NL.
--   $$
--
--   This is the same wire-bound certificate as `net0O2_W1F_wires_lt_NL`, restated against `IntMul_Kappa_R8_Data_BitOppbankQHNetRec`. Combined with $\mathrm{genF}$ local-preservation it is the data-bound leaf of the $\mathrm{cs1}$ touch densify in the QHNetRec environment.
--
--   **Formalization Note.** Bounds follow from layout identities $w_X(t)=t$, $w_Y(T)=v+T$, $w_S(q)=w_{\mathrm{Ent}}+q$, $w_T(c)=w_{\mathrm{AuxEnd}}+c$ together with the QHNetRec LocSlots certificates $\mathrm{injS},\mathrm{srcS},\mathrm{retS}<NR$, $\mathrm{pts}<h$, and $\mathrm{recs}$ slots $<NR$. The statement does not import the parent module `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`. Layout lemmas may be imported from the already-proved `net0O2_layout_wires_lt_NL`, which does not depend on `QHNet`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: W1F LocSlots wire bound, restated on the total-decoder fork IntMul_Kappa_R8_Data_BitOppbankQHNetRec (d127abea). Does not close or replace 7092591a-7d51-4401-98dc-91af9889af44.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NL)
theorem net0O2_W1F_wires_lt_NL_rec (ℓ : ℕ)
    (hℓ : ∃ i ∈ W1F, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) :
    ℓ < NL := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
