-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayQuotient_toFullRay_injective
-- name    : OAI.SevenEighths.RayQuotient.toFullRay_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:01:02.979213+00:00
-- url     : https://prove2.me/theorems/f5a1ad9d-36b5-437f-b832-874e105a5c1f
-- title:
--   Ray Quotient: to Full Ray injective
-- statement:
--   The Ray Quotient construction uses the to Full Ray injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean#L30-L32
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean#L30-L32

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)
include hH

theorem OAI.SevenEighths.RayQuotient.toFullRay_injective : Function.Injective (toFullRay M H hH) := by sorry
