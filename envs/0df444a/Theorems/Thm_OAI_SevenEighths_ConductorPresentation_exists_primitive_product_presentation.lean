-- Prove2me | Theorems.Thm_OAI_SevenEighths_ConductorPresentation_exists_primitive_product_presentation
-- name    : OAI.SevenEighths.ConductorPresentation.exists_primitive_product_presentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:36.303226+00:00
-- url     : https://prove2.me/theorems/bcda407c-4b66-41d8-9f4a-07c1d77f7aa8
-- title:
--   Conductor Presentation: exists primitive product presentation
-- statement:
--   The Conductor Presentation construction uses the exists primitive product presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean#L127-L147
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorPresentation.lean#L127-L147

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

theorem OAI.SevenEighths.ConductorPresentation.exists_primitive_product_presentation
    (M L₁ L₂ : Ideal A) [Finite (A ⧸ M)] (hML₁ : M ≤ L₁) (hML₂ : M ≤ L₂)
    (χ ψ : MulChar (A ⧸ M) ℂ)
    (hχ : FactorsThroughIdeal χ (L₁.map (Ideal.Quotient.mk M)))
    (hψ : FactorsThroughIdeal ψ (L₂.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L₁ ⊓ L₂ ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.cardQuot ≤ L₁.cardQuot * L₂.cardQuot ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) * ψ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by sorry
