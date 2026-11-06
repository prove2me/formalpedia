-- Prove2me | Theorems.Thm_OAI_SevenEighths_IdealCharacter_isUnit_mk_iff_isCoprime
-- name    : OAI.SevenEighths.IdealCharacter.isUnit_mk_iff_isCoprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:58:33.450218+00:00
-- url     : https://prove2.me/theorems/73a77a70-3aae-4da1-8178-934b0283866b
-- title:
--   Ideal Character: is Unit mk iff is Coprime
-- statement:
--   The Ideal Character construction uses the is Unit mk iff is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L26-L42
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L26-L42

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

theorem OAI.SevenEighths.IdealCharacter.isUnit_mk_iff_isCoprime (M : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk M a) ↔ IsCoprime (Ideal.span ({a} : Set A)) M := by sorry
