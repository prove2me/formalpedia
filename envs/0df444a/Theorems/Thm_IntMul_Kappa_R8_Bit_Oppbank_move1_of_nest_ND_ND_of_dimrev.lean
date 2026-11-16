-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_of_nest_ND_ND_of_dimrev
-- name    : IntMul.Kappa.R8.Bit.Oppbank.move1_of_nest_ND_ND_of_dimrev
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T10:07:49.689008+00:00
-- url     : https://prove2.me/theorems/2c74a450-45bb-42dd-9bd9-6eb0c5160fb0
-- title:
--   Reverse strict-dim ND–ND nest implies the stage-one move
-- statement:
--   # Reverse strict-dimension ND–ND nest implies the stage-one move
--
--   Let $S,S_i$ be mutually inverse encodings, and let $o,c$ be ND codes with $\mathrm{nestOK}(o,c)$ and $b<1771$. If
--
--   $$\dim_{\mathrm{CF}}(c)<\dim_{\mathrm{CF}}(o),$$
--
--   then
--
--   $$\mathrm{pswQ}\bigl(K(S,S_i,D_m(o,c),P_\ell(b))\bigr)\,\Phi_1(S,S_i,b,o)=\Phi_1(S,S_i,b,c).$$
--
--   The strict dimension hypothesis excludes the 1770 equal-dimension leaf counterexamples that block a universal nestOK move on published Pnd.
--
--   Formalization note. The proof uses the already-proved `nestOK_symm` to swap the nest, `nest_Le_ND_ND_of_dim` to obtain $\mathrm{Le}(P_c(c),P_c(o))$, and the right disjunct of `move1_of_Le_dim`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: reverse strict-dim ND-ND nestOK move1 on published Pnd.

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
/-- Stage-one move on an ND–ND nest with *strict* `dimCF c < dimCF o`.
    Excludes the 1770 equal-dim leaf counterexamples. -/
theorem move1_of_nest_ND_ND_of_dimrev
    (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {o c b : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hb : b < 1771)
    (hok : nestOK o c = true)
    (hNDo : isND o = true) (hNDc : isND c = true)
    (hdim : dimCF c < dimCF o) :
    pswQ (K S Si (Dm o c) (Pl b)) * Φ₁ S Si b o = Φ₁ S Si b c := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
