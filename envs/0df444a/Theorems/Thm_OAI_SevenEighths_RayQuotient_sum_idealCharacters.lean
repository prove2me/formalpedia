-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayQuotient_sum_idealCharacters
-- name    : OAI.SevenEighths.RayQuotient.sum_idealCharacters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:07:45.98878+00:00
-- url     : https://prove2.me/theorems/3b58bb7e-ee16-4526-96e2-86d0faf64f69
-- title:
--   Ray Quotient: sum ideal Characters
-- statement:
--   The Ray Quotient construction uses the sum ideal Characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean#L83-L92
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean#L83-L92

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_idealCharacters

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)
include hH
variable [IsDomain A] [IsPrincipalIdealRing A]

theorem OAI.SevenEighths.RayQuotient.sum_idealCharacters (I : Ideal A) :
    ∑ χ : Characters M H, idealCharacter M H hH χ I =
      if I ∈ identityClass M H then (classNumber M H : ℂ) else 0 := by sorry
