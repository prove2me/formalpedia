-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_inflate_trans
-- name    : OAI.SevenEighths.ResidueCharacter.inflate_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:45.682374+00:00
-- url     : https://prove2.me/theorems/79fa25e0-ff94-4a92-bdcd-4336f1a8521a
-- title:
--   Residue Character: inflate trans
-- statement:
--   The Residue Character construction uses the inflate trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L56-L65
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L56-L65

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

theorem OAI.SevenEighths.ResidueCharacter.inflate_trans {M L K : Ideal A} (hML : M ≤ L) (hLK : L ≤ K)
    (χ : MulChar (A ⧸ K) ℂ) :
    inflate hML (inflate hLK χ) = inflate (hML.trans hLK) χ := by sorry
