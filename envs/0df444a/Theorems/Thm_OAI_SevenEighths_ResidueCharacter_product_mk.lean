-- Prove2me | Theorems.Thm_OAI_SevenEighths_ResidueCharacter_product_mk
-- name    : OAI.SevenEighths.ResidueCharacter.product_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:05.874536+00:00
-- url     : https://prove2.me/theorems/401f4261-518b-4555-ac3b-60098a621e3b
-- title:
--   Residue Character: product mk
-- statement:
--   The Residue Character construction uses the product mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L117-L129
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ResidueCharacter.lean#L117-L129

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

theorem OAI.SevenEighths.ResidueCharacter.product_mk (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ)
    (a : A) :
    product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) a) =
      χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) := by sorry
