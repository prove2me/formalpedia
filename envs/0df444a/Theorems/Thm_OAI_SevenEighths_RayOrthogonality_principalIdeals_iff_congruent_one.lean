-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_principalIdeals_iff_congruent_one
-- name    : OAI.SevenEighths.RayOrthogonality.principalIdeals_iff_congruent_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:36.033382+00:00
-- url     : https://prove2.me/theorems/58694910-fe12-4578-a4d6-9bdb1a81dcc7
-- title:
--   Ray Orthogonality: principal Ideals iff congruent one
-- statement:
--   The Ray Orthogonality construction uses the principal Ideals iff congruent one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L164-L179
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L164-L179

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
omit [Finite (A ⧸ M)] [IsPrincipalIdealRing A]

theorem OAI.SevenEighths.RayOrthogonality.principalIdeals_iff_congruent_one (I : Ideal A) :
    I ∈ principalIdeals M ↔ ∃ a : A, a ≠ 0 ∧
      Ideal.span ({a} : Set A) = I ∧ Ideal.Quotient.mk M a = 1 := by sorry
