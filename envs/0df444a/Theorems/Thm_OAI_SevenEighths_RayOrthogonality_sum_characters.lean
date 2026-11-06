-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_characters
-- name    : OAI.SevenEighths.RayOrthogonality.sum_characters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:59:58.61945+00:00
-- url     : https://prove2.me/theorems/f808bc9b-cd4e-4384-afa4-18ba9e4d68bc
-- title:
--   Ray Orthogonality: sum characters
-- statement:
--   The Ray Orthogonality construction uses the sum characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L59-L74
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L59-L74

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {R : Type*} [CommMonoid R] [Finite R]

theorem OAI.SevenEighths.RayOrthogonality.sum_characters (H : Subgroup Rˣ) (r : R) :
    ∑ χ : characters H, (χ : MulChar R ℂ) r =
      if inUnitSubgroup H r then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by sorry
