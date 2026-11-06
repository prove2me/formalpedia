-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_rayCharacters
-- name    : OAI.SevenEighths.RayOrthogonality.sum_rayCharacters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:10.630821+00:00
-- url     : https://prove2.me/theorems/bf564002-547c-4552-a0fd-17a053cd9f05
-- title:
--   Ray Orthogonality: sum ray Characters
-- statement:
--   The Ray Orthogonality construction uses the sum ray Characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L123-L126
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L123-L126

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]

theorem OAI.SevenEighths.RayOrthogonality.sum_rayCharacters (r : A ⧸ M) :
    ∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r =
      if principalResidue M r then (rayCard M : ℂ) else 0 := by sorry
