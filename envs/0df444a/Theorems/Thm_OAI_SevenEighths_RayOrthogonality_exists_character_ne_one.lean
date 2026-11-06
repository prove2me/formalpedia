-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_exists_character_ne_one
-- name    : OAI.SevenEighths.RayOrthogonality.exists_character_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:03.586876+00:00
-- url     : https://prove2.me/theorems/184abf52-9ce8-4461-92c9-7b138bb70018
-- title:
--   Ray Orthogonality: exists character ne one
-- statement:
--   The Ray Orthogonality construction uses the exists character ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L28-L37
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L28-L37

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {R : Type*} [CommMonoid R] [Finite R]

theorem OAI.SevenEighths.RayOrthogonality.exists_character_ne_one (H : Subgroup Rˣ) {u : Rˣ} (hu : u ∉ H) :
    ∃ χ : characters H, (χ : MulChar R ℂ) u ≠ 1 := by sorry
