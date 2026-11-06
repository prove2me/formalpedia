-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_factorsThrough
-- name    : OAI.SevenEighths.ResidueCharacter.inflate_factorsThrough
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:44.976897+00:00
-- url     : https://prove2.me/theorems/249fe178-cfe7-44ef-923d-e4ed00b3dd35
-- title:
--   Residue Character: inflate factors Through
-- statement:
--   The Residue Character construction uses the inflate factors Through property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L43-L54
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L43-L54

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

theorem OAI.SevenEighths.ResidueCharacter.inflate_factorsThrough {M L : Ideal A} [Finite (A ⧸ M)]
    (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    FactorsThroughIdeal (inflate hML χ) (L.map (Ideal.Quotient.mk M)) := by sorry
