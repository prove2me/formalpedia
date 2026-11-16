-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_layout_wires_lt_NL
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_layout_wires_lt_NL
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:15:21.479835+00:00
-- url     : https://prove2.me/theorems/eb4962cb-1054-412e-8997-03dbdb86fe6f
-- title:
--   Local layout maps $w_X,w_Y,w_S,w_T$ send their domains below $NL$
-- statement:
--   The four densified local-wire layout maps send their intended domains into the local address space $[0,NL)$.
--
--   With the R8 opp-bank constants $v=1771$, $NR=27794$, $h=23$, $w_{\mathrm{Ent}}=3542$, $w_{\mathrm{AuxEnd}}=31336$, and $NL=31359$,
--   $$
--   \begin{aligned}
--   t < v &\implies w_X(t) < NL,\\
--   T < v &\implies w_Y(T) < NL,\\
--   q < NR &\implies w_S(q) < NL,\\
--   c < h &\implies w_T(c) < NL.
--   \end{aligned}
--   $$
--
--   These maps are the layout identities $w_X(t)=t$, $w_Y(T)=v+T$, $w_S(q)=w_{\mathrm{Ent}}+q$, and $w_T(c)=w_{\mathrm{AuxEnd}}+c$. They are the arithmetic ingredients that turn LocSlots index certificates into the $W_{1F}$ wire bound $\ell<NL$.
--
--   **Formalization Note.** Constants and maps are those of `Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout`. The four conjuncts correspond to the local lemmas `wX_lt_NL`, `wY_lt_NL`, `wS_lt_NL`, and `wT_lt_NL`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: wire layout maps wX/wY/wS/wT (Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout, NL=31359)

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
theorem net0O2_layout_wires_lt_NL :
    (∀ t : ℕ, t < v → wX t < NL) ∧
    (∀ T : ℕ, T < v → wY T < NL) ∧
    (∀ q : ℕ, q < NR → wS q < NL) ∧
    (∀ c : ℕ, c < h → wT c < NL) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
