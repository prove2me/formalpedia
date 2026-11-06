-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_norm_idealCharacter_le_one
-- name    : OAI.SevenEighths.RayOrthogonality.norm_idealCharacter_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:30.633667+00:00
-- url     : https://prove2.me/theorems/712de891-366f-41b2-93aa-59ab64cf4885
-- title:
--   Ray Orthogonality: norm ideal Character le one
-- statement:
--   The Ray Orthogonality construction uses the norm ideal Character le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L181-L182
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L181-L182

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

theorem OAI.SevenEighths.RayOrthogonality.norm_idealCharacter_le_one (χ : rayCharacters M) (I : Ideal A) :
    ‖idealCharacter M χ I‖ ≤ 1 := by sorry
