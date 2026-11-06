-- Prove2me | Theorems.Thm_OAI_SevenEighths_ConductorPresentation_comap_ne_bot
-- name    : OAI.SevenEighths.ConductorPresentation.comap_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:50.632214+00:00
-- url     : https://prove2.me/theorems/6d2a80a4-d5ab-483b-9edf-50562bc8a0d7
-- title:
--   Conductor Presentation: comap ne bot
-- statement:
--   The Conductor Presentation construction uses the comap ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean#L78-L87
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean#L78-L87

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
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite

theorem OAI.SevenEighths.ConductorPresentation.comap_ne_bot (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    I.comap (Ideal.Quotient.mk M) ≠ ⊥ := by sorry
