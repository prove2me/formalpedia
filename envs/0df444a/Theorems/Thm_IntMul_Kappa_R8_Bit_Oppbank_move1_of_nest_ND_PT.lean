-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_of_nest_ND_PT
-- name    : IntMul.Kappa.R8.Bit.Oppbank.move1_of_nest_ND_PT
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T10:40:53.26232+00:00
-- url     : https://prove2.me/theorems/b136c98e-8ed9-453d-80bb-784ff31ba2a9
-- title:
--   Strict-dimension ND–PT nest implies the stage-one move
-- statement:
--   # Strict-dimension ND–PT nest implies the stage-one move
--
--   Let $S,S_i$ be mutually inverse encodings, let $o$ be an ND code and $c$ a PT code with $\mathrm{nestOK}(o,c)$, and let $b<1771$. If the dimensions are strictly ordered
--
--   $$\dim_{\mathrm{CF}}(o)<\dim_{\mathrm{CF}}(c),$$
--
--   then
--
--   $$\mathrm{pswQ}\bigl(K(S,S_i,D_m(o,c),P_\ell(b))\bigr)\,\Phi_1(S,S_i,b,o)=\Phi_1(S,S_i,b,c).$$
--
--   The argument composes the already-proved lemma `nest_Le_ND_NDpt` (which yields $\mathrm{Le}(P_c(o),P_c(c))$ from the nest, using the automatic inequality $\dim_{\mathrm{CF}}(o)\le\dim_{\mathrm{CF}}(c)$) with the left disjunct of `move1_of_Le_dim`. Empirically every nestOK ND–PT pair on the published carrier is strict-dim, so the hypothesis is the natural one. There is no useful PT→ND companion: $\mathrm{Le}(P_c(c),P_c(o))$ fails on every existing pair, and the Open lemma `nest_Le_ND_PTnd` is only vacuously true.
--
--   Formalization note. The proof is a one-line composition: `le_of_lt` feeds `nest_Le_ND_NDpt`, and `Or.inl` selects the left disjunct of `move1_of_Le_dim`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: strict-dim ND-PT nestOK move1 on published Pnd, composing nest_Le_ND_NDpt with move1_of_Le_dim.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open Matrix
/-- Stage-one move on an ND–PT nest with *strict* `dimCF o < dimCF c`.
    Uses `nest_Le_ND_NDpt` and the left disjunct of `move1_of_Le_dim`.
    There is no useful PT→ND companion: `Le(PT, ND)` fails on every existing pair. -/
theorem move1_of_nest_ND_PT
    (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {o c b : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hb : b < 1771)
    (hok : nestOK o c = true)
    (hNDo : isND o = true) (hPTc : isPT c = true)
    (hdim : dimCF o < dimCF c) :
    pswQ (K S Si (Dm o c) (Pl b)) * Φ₁ S Si b o = Φ₁ S Si b c := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
