-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_isUnit_mk_inf_iff
-- name    : OAI.SevenEighths.ResidueCharacter.isUnit_mk_inf_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:52.873737+00:00
-- url     : https://prove2.me/theorems/56d86b58-9f25-49c0-90c1-ce5f2b4936b1
-- title:
--   Residue Character: is Unit mk inf iff
-- statement:
--   The Residue Character construction uses the is Unit mk inf iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L74-L99
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L74-L99

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

theorem OAI.SevenEighths.ResidueCharacter.isUnit_mk_inf_iff (I J : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk (I ⊓ J) a) ↔
      IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a) := by sorry
