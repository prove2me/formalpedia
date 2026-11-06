-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_average_idealCharacters
-- name    : OAI.SevenEighths.RayOrthogonality.average_idealCharacters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:28.267398+00:00
-- url     : https://prove2.me/theorems/7f3ebaa5-a13f-441c-8f63-489f27e3916e
-- title:
--   Ray Orthogonality: average ideal Characters
-- statement:
--   The Ray Orthogonality construction uses the average ideal Characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L200-L205
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L200-L205

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
variable [IsDomain A] [IsPrincipalIdealRing A]

theorem OAI.SevenEighths.RayOrthogonality.average_idealCharacters (I : Ideal A) :
    (∑ χ : rayCharacters M, idealCharacter M χ I) / (rayCard M : ℂ) =
      if I ∈ principalIdeals M then 1 else 0 := by sorry
