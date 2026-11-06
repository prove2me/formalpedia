-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_idealCharacters
-- name    : OAI.SevenEighths.RayOrthogonality.sum_idealCharacters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:13.237421+00:00
-- url     : https://prove2.me/theorems/dd6c6d97-24db-4c08-a951-288b76bb9a3b
-- title:
--   Ray Orthogonality: sum ideal Characters
-- statement:
--   The Ray Orthogonality construction uses the sum ideal Characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L189-L198
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L189-L198

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

theorem OAI.SevenEighths.RayOrthogonality.sum_idealCharacters (I : Ideal A) :
    ∑ χ : rayCharacters M, idealCharacter M χ I =
      if I ∈ principalIdeals M then (rayCard M : ℂ) else 0 := by sorry
