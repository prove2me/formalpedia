-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_characters_unit
-- name    : OAI.SevenEighths.RayOrthogonality.sum_characters_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:17.180874+00:00
-- url     : https://prove2.me/theorems/d0ec4089-cd95-4ba0-96e6-19bf97d8d840
-- title:
--   Ray Orthogonality: sum characters unit
-- statement:
--   The Ray Orthogonality construction uses the sum characters unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L39-L54
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L39-L54

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {R : Type*} [CommMonoid R] [Finite R]

theorem OAI.SevenEighths.RayOrthogonality.sum_characters_unit (H : Subgroup Rˣ) (u : Rˣ) :
    ∑ χ : characters H, (χ : MulChar R ℂ) u =
      if u ∈ H then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by sorry
