-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayQuotient_identityClass_iff_generator
-- name    : OAI.SevenEighths.RayQuotient.identityClass_iff_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:01:09.788206+00:00
-- url     : https://prove2.me/theorems/f5c76d62-ecec-4f0c-8071-a86b71bc51c8
-- title:
--   Ray Quotient: identity Class iff generator
-- statement:
--   The Ray Quotient construction uses the identity Class iff generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean#L52-L72
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean#L52-L72

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
variable [IsDomain A] [IsPrincipalIdealRing A]
omit [Finite (A ⧸ M)]

theorem OAI.SevenEighths.RayQuotient.identityClass_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ identityClass M H ↔
      inUnitSubgroup H (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by sorry
