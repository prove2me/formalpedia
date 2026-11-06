-- Prove2me | Theorems.Thm_OAI_SevenEighths_ConductorPresentation_exists_primitive_presentation
-- name    : OAI.SevenEighths.ConductorPresentation.exists_primitive_presentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:21.232417+00:00
-- url     : https://prove2.me/theorems/88a9681f-dc92-453b-942e-5dc32672348c
-- title:
--   Conductor Presentation: exists primitive presentation
-- statement:
--   The Conductor Presentation construction uses the exists primitive presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean#L105-L114
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean#L105-L114

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

theorem OAI.SevenEighths.ConductorPresentation.exists_primitive_presentation (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.cardQuot ≤ M.cardQuot ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by sorry
