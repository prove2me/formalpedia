-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_toUnitHom
-- name    : OAI.SevenEighths.ResidueCharacter.inflate_toUnitHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:44.941044+00:00
-- url     : https://prove2.me/theorems/b4034cfc-a6b5-4b9f-8e97-420c8fba779e
-- title:
--   Residue Character: inflate to Unit Hom
-- statement:
--   The Residue Character construction uses the inflate to Unit Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L20-L23
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L20-L23

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

theorem OAI.SevenEighths.ResidueCharacter.inflate_toUnitHom {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    (inflate hML χ).toUnitHom =
      χ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hML).toMonoidHom) := by sorry
