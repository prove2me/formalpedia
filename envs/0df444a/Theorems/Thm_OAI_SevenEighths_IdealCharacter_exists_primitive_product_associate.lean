-- Prove2me | Theorems.Thm_OAI_SevenEighths_IdealCharacter_exists_primitive_product_associate
-- name    : OAI.SevenEighths.IdealCharacter.exists_primitive_product_associate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:58:32.42261+00:00
-- url     : https://prove2.me/theorems/f01352b1-df3b-4c53-a5d7-43efd2aa27ad
-- title:
--   Ideal Character: exists primitive product associate
-- statement:
--   The Ideal Character construction uses the exists primitive product associate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L230-L249
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L230-L249

import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.IdealCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
variable [IsDomain A] [IsPrincipalIdealRing A]
variable [hInfinite : Infinite A]
include hInfinite

theorem OAI.SevenEighths.IdealCharacter.exists_primitive_product_associate (M N : Ideal A)
    [Finite (A ⧸ M)] [Finite (A ⧸ N)]
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ⊓ N ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.cardQuot ≤ M.cardQuot * N.cardQuot ∧
      (∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        if IsCoprime I (M ⊓ N) then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        ofResidue (M ⊓ N) 1 (one_unitInvariant (M ⊓ N)) I * ofResidue K φ hφ I := by sorry
