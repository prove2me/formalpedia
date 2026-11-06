-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_idealCharacter_one
-- name    : OAI.SevenEighths.RayOrthogonality.idealCharacter_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:33.594656+00:00
-- url     : https://prove2.me/theorems/cca55d1d-4423-4d4d-adb6-0ff536500693
-- title:
--   Ray Orthogonality: ideal Character one
-- statement:
--   The Ray Orthogonality construction uses the ideal Character one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L184-L187
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L184-L187

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

theorem OAI.SevenEighths.RayOrthogonality.idealCharacter_one (I : Ideal A) :
    idealCharacter M 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 := by sorry
