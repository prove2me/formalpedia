-- Prove2me | Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_product
-- name    : OAI.SevenEighths.IdealCharacter.ofResidue_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:58:39.040198+00:00
-- url     : https://prove2.me/theorems/f413dc73-03b9-4403-a414-03adba4f1d56
-- title:
--   Ideal Character: of Residue product
-- statement:
--   The Ideal Character construction uses the of Residue product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L194-L206
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L194-L206

import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_product_global_units

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

theorem OAI.SevenEighths.IdealCharacter.ofResidue_product (M N : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) (I : Ideal A) :
    ofResidue (M ⊓ N) (ResidueCharacter.product M N χ ψ)
        (ResidueCharacter.product_global_units M N χ ψ hχ hψ) I =
      ofResidue M χ hχ I * ofResidue N ψ hψ I := by sorry
