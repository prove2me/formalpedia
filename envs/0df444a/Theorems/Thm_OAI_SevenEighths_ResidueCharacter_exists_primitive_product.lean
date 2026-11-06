-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_exists_primitive_product
-- name    : OAI.SevenEighths.ResidueCharacter.exists_primitive_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:24.492575+00:00
-- url     : https://prove2.me/theorems/fdb732e5-6498-4069-b5ba-dd01c2a6d321
-- title:
--   Residue Character: exists primitive product
-- statement:
--   The Residue Character construction uses the exists primitive product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L144-L157
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L144-L157

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
variable [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite

theorem OAI.SevenEighths.ResidueCharacter.exists_primitive_product (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)]
    (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.cardQuot ≤ I.cardQuot * J.cardQuot ∧
      ∀ a : A, χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) =
        if IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a)
          then φ (Ideal.Quotient.mk K a) else 0 := by sorry
