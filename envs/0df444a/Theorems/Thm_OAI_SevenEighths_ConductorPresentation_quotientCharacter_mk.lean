-- Prove2me | Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
-- name    : OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:25.864036+00:00
-- url     : https://prove2.me/theorems/870760e1-1dfe-4769-887c-e630c656cc0d
-- title:
--   Conductor Presentation: quotient Character mk
-- statement:
--   The Conductor Presentation construction uses the quotient Character mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean#L41-L44
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
set_option autoImplicit false
open OAI
open OAI.SevenEighths
open OAI.SevenEighths.ConductorPresentation
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]

theorem OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (a : A) :
    quotientCharacter M I φ (Ideal.Quotient.mk _ a) =
      φ (Ideal.Quotient.mk I (Ideal.Quotient.mk M a)) := by sorry

attribute [defeq] OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk
