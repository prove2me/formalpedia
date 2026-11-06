-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_mk
-- name    : OAI.SevenEighths.ResidueCharacter.inflate_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:10.727852+00:00
-- url     : https://prove2.me/theorems/dd142a61-d9b8-49d3-97dc-36181cb69753
-- title:
--   Residue Character: inflate mk
-- statement:
--   The Residue Character construction uses the inflate mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L38-L41
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L38-L41

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.ResidueCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]

theorem OAI.SevenEighths.ResidueCharacter.inflate_mk {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) (a : A) :
    inflate hML χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then χ (Ideal.Quotient.mk L a) else 0 := by sorry
