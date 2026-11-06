-- Prove2me | Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
-- name    : OAI.SevenEighths.IdealCharacter.ofResidue_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:58:28.921121+00:00
-- url     : https://prove2.me/theorems/5bf6d548-bcc9-4061-8668-5e231857b444
-- title:
--   Ideal Character: of Residue bot
-- statement:
--   The Ideal Character construction uses the of Residue bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L92-L93
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/IdealCharacter.lean#L92-L93

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

theorem OAI.SevenEighths.IdealCharacter.ofResidue_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : ofResidue M χ hχ ⊥ = 0 := by sorry
