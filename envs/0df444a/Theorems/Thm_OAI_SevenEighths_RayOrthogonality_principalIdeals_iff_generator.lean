-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_principalIdeals_iff_generator
-- name    : OAI.SevenEighths.RayOrthogonality.principalIdeals_iff_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:06.158648+00:00
-- url     : https://prove2.me/theorems/00f8bfb8-a3a3-4680-9d23-0f09cc3bced8
-- title:
--   Ray Orthogonality: principal Ideals iff generator
-- statement:
--   The Ray Orthogonality construction uses the principal Ideals iff generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L144-L160
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L144-L160

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
omit [Finite (A ⧸ M)]

theorem OAI.SevenEighths.RayOrthogonality.principalIdeals_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ principalIdeals M ↔
      principalResidue M (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by sorry
