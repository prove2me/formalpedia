-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_average_characters
-- name    : OAI.SevenEighths.RayOrthogonality.average_characters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:02.638842+00:00
-- url     : https://prove2.me/theorems/3a15edfb-f141-4e6f-8170-a88a83912c02
-- title:
--   Ray Orthogonality: average characters
-- statement:
--   The Ray Orthogonality construction uses the average characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L79-L85
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L79-L85

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {R : Type*} [CommMonoid R] [Finite R]

theorem OAI.SevenEighths.RayOrthogonality.average_characters (H : Subgroup Rˣ) (r : R) :
    (∑ χ : characters H, (χ : MulChar R ℂ) r) / (Nat.card (Rˣ ⧸ H) : ℂ) =
      if inUnitSubgroup H r then 1 else 0 := by sorry
