-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_ND_of_dim
-- name    : IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND_ND_of_dim
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:53:17.440853+00:00
-- url     : https://prove2.me/theorems/68ecf6c8-80a5-4530-9174-b71112027f8b
-- title:
--   Strict-dim ND–ND nest implies Le (Pc o) (Pc c)
-- statement:
--   # Strict-dimension ND–ND nest implies $\mathrm{Le}(P_c(o),P_c(c))$
--
--   Let $o,c$ be codes strictly below $\mathrm{codeBound}=64251$, both ND, with $\mathrm{nestOK}(o,c)$. If the dimensions are strictly ordered,
--
--   $$\dim_{\mathrm{CF}}(o)<\dim_{\mathrm{CF}}(c),$$
--
--   then $\mathrm{Le}(P_c(o),P_c(c))$, i.e. $P_c(c)\,P_c(o)=P_c(o)$ and $P_c(o)\,P_c(c)=P_c(o)$.
--
--   The strict dimension hypothesis excludes the 1770 equal-dimension leaf counterexamples of the non-strict form, which is false on published Pnd.
--
--   Formalization note. The proof composes the already-proved lemmas `dimCF_of_ND`, `densSup_land_mono_of_argRel_of_dim`, `argRel_dim_le`, `Le_Pnd_of_land`, and `AllDensCentred` on published (non-Fix) Pnd. `Le` is the projector-order relation from MoveFacts2.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: strict-dim nest_Le_ND_ND on published Pnd.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG

/-- Strict-dim ND–ND nest: if `dimCF o < dimCF c`, then `Le (Pc o) (Pc c)`.
    Excludes the 1770 equal-dim leaf counterexamples of the non-strict form. -/
theorem nest_Le_ND_ND_of_dim :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      isND o = true → isND c = true → dimCF o < dimCF c → Le (Pc o) (Pc c) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
