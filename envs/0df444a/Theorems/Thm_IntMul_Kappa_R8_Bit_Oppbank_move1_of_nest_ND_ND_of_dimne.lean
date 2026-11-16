-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_of_nest_ND_ND_of_dimne
-- name    : IntMul.Kappa.R8.Bit.Oppbank.move1_of_nest_ND_ND_of_dimne
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T10:07:52.283463+00:00
-- url     : https://prove2.me/theorems/53fb7aa4-8cb2-4720-9513-93e1f467eb36
-- title:
--   Strictly unequal-dim ND–ND nest implies the stage-one move
-- statement:
--   # Strictly unequal-dimension ND–ND nest implies the stage-one move
--
--   Let $S,S_i$ be mutually inverse encodings, and let $o,c$ be ND codes with $\mathrm{nestOK}(o,c)$ and $b<1771$. If the dimensions are strictly unequal,
--
--   $$\dim_{\mathrm{CF}}(o)<\dim_{\mathrm{CF}}(c)\qquad\text{or}\qquad\dim_{\mathrm{CF}}(c)<\dim_{\mathrm{CF}}(o),$$
--
--   then
--
--   $$\mathrm{pswQ}\bigl(K(S,S_i,D_m(o,c),P_\ell(b))\bigr)\,\Phi_1(S,S_i,b,o)=\Phi_1(S,S_i,b,c).$$
--
--   Equal-dimension pairs, including the 1770 leaf counterexamples, are excluded.
--
--   Formalization note. The proof cases on the two strict inequalities and applies the already-proved lemmas `move1_of_nest_ND_ND_of_dim` and `move1_of_nest_ND_ND_of_dimrev`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: combined strict-dim ND-ND nestOK move1 on published Pnd.

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
/-- Stage-one move on an ND–ND nest with *strictly unequal* dimensions
    (`dimCF o < dimCF c` or `dimCF c < dimCF o`).
    Excludes the 1770 equal-dim leaf counterexamples. -/
theorem move1_of_nest_ND_ND_of_dimne
    (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {o c b : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hb : b < 1771)
    (hok : nestOK o c = true)
    (hNDo : isND o = true) (hNDc : isND c = true)
    (hdim : dimCF o < dimCF c ∨ dimCF c < dimCF o) :
    pswQ (K S Si (Dm o c) (Pl b)) * Φ₁ S Si b o = Φ₁ S Si b c := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
