-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_apply_unit
-- name    : OAI.SevenEighths.ResidueCharacter.inflate_apply_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:32.989173+00:00
-- url     : https://prove2.me/theorems/0cc7087e-c6bd-4007-81d8-52e30fdd3663
-- title:
--   Residue Character: inflate apply unit
-- statement:
--   The Residue Character construction uses the inflate apply unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L25-L28
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L25-L28

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

theorem OAI.SevenEighths.ResidueCharacter.inflate_apply_unit {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (u : (A ⧸ M)ˣ) :
    inflate hML χ u = χ (Ideal.Quotient.factor hML (u : A ⧸ M)) := by sorry
