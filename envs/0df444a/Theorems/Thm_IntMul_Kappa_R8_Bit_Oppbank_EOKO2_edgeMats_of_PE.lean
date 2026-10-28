-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO2_edgeMats_of_PE
-- name    : IntMul.Kappa.R8.Bit.Oppbank.EOKO2_edgeMats_of_PE
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:52:36.809893+00:00
-- url     : https://prove2.me/theorems/5e7a20ef-7682-4d01-bb4c-4323abbb9e34
-- title:
--   EOKO2 edge-matrix identities from OneRun2 PE inhabitance
-- statement:
--   # EOKO2 edge matrices from PE
--
--   Assuming OneRun2 PE inhabitance of all channel families, a prime bound $q_0$ yields the six $\mathrm{EOKO2}$ edge-matrix identities at $N=q^f$ (via proved `edgeMat_eq` and `good_mats`).
--
--   **Formalization Note.** OneRun2 analogue of proved `EOKO_edgeMats_of_PE` `9991cdfb`.
-- source:
--   edgeMat_eq c37fb424; OneRunFormalOK2; EOKOPack2

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (Dm Pl nestOK K rkC)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2 (PE oneRun)
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)
theorem EOKO2_edgeMats_of_PE
    (hPE :
      (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        ∃ e, PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c)) e) ∧
      (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c)) e) ∧
      (∀ b < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22) e) ∧
      (∀ a < 1771, ∀ t < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484) e) ∧
      (∀ a < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22) e) ∧
      (∀ a < 1771, ∀ s < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1) e)) :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f,
      let N := q ^ f
      (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        edgeMat N (ch0NB.e1 b o c) = redM N (pswQ (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)))) ∧
      (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        edgeMat N (ch0NB.e2 a o c) = redM N (pswQ (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)))) ∧
      (∀ b < 1771, edgeMat N (ch0NB.ex b) = redM N (pswQ (K ch0NB.S ch0NB.Si 1 (1 - Pl b)))) ∧
      (∀ a < 1771, ∀ t < 1771, edgeMat N (ch0NB.en a t) =
        redM N (pswQ (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)))) ∧
      (∀ a < 1771, edgeMat N (ch0NB.ei a) = redM N (pswQ (K ch0NB.S ch0NB.Si (1 - Pl a) 1))) ∧
      (∀ a < 1771, ∀ s < 1771, edgeMat N (ch0NB.ec a s) =
        redM N (pswQ (K ch0NB.S ch0NB.Si (Pl a) (Pl s)))) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
