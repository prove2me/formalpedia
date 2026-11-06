-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_finite_quotient_inf
-- name    : OAI.SevenEighths.ResidueCharacter.finite_quotient_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:37.26108+00:00
-- url     : https://prove2.me/theorems/40355119-ef63-4419-b321-7baa9be5d67e
-- title:
--   Residue Character: finite quotient inf
-- statement:
--   The Residue Character construction uses the finite quotient inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L101-L111
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L101-L111

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

theorem OAI.SevenEighths.ResidueCharacter.finite_quotient_inf (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    Finite (A ⧸ I ⊓ J) := by sorry
