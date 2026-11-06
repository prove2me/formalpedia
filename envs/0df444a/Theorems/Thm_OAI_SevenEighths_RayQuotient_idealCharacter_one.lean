-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayQuotient_idealCharacter_one
-- name    : OAI.SevenEighths.RayQuotient.idealCharacter_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:01:52.801149+00:00
-- url     : https://prove2.me/theorems/d7f0f629-7e6e-4b44-aad9-999ef3dcf1dc
-- title:
--   Ray Quotient: ideal Character one
-- statement:
--   The Ray Quotient construction uses the ideal Character one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean#L78-L81
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean#L78-L81

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_idealCharacter_one

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

theorem OAI.SevenEighths.RayQuotient.idealCharacter_one (I : Ideal A) :
    idealCharacter M H hH 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 := by sorry
