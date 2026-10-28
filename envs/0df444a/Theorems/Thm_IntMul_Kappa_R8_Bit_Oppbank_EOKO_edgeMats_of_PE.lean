-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO_edgeMats_of_PE
-- name    : IntMul.Kappa.R8.Bit.Oppbank.EOKO_edgeMats_of_PE
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:19:17.517154+00:00
-- url     : https://prove2.me/theorems/9991cdfb-b22c-4d5d-9df7-e8ee255b91e7
-- title:
--   EOKO edge-matrix identities from one-run PE inhabitance
-- statement:
--   # Edge-matrix identities from PE inhabitance
--
--   Assuming every densified one-run channel family is PE-inhabited, there is a prime bound $q_0$ such that for all primes $q>q_0$ and all powers $f$, the six $\mathrm{EOKO}$ edge-matrix identities hold at $N=q^f$ (via $\mathrm{edgeMat\_eq}$ and denominator control on the finite Bruhat-factor pack).
--
--   **Formalization Note.** Packaging lemma between `EOKO_oneRun_PE_families` and `EOKO_edgeMats_large2`.
-- source:
--   edgeMat_eq c37fb424; good_mats ff209901; OneRunFormalOK E0

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (Dm Pl nestOK K rkC)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet (PE oneRun)
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)
theorem EOKO_edgeMats_of_PE
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
