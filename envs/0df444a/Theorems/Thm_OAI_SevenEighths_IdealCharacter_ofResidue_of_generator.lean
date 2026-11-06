-- Prove2me | Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_of_generator
-- name    : OAI.SevenEighths.IdealCharacter.ofResidue_of_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:58:33.376328+00:00
-- url     : https://prove2.me/theorems/b53c0b76-02cb-4457-b427-5e719452b1ff
-- title:
--   Ideal Character: of Residue of generator
-- statement:
--   The Ideal Character construction uses the of Residue of generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L100-L108
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L100-L108

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

theorem OAI.SevenEighths.IdealCharacter.ofResidue_of_generator (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {I : Ideal A} (hI : I ≠ ⊥) {a : A}
    (ha : Ideal.span ({a} : Set A) = I) :
    ofResidue M χ hχ I = χ (Ideal.Quotient.mk M a) := by sorry
