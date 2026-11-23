-- Prove2me | Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- name    : GlobalTheory.orthogonalQuotientForm_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:47.361676+00:00
-- url     : https://prove2.me/theorems/52f0c3a8-72cf-4928-be2f-40c2d0346b2c
-- title:
--   Global Theory: orthogonal Quotient Form mk
-- statement:
--   The Global Theory construction uses the orthogonal Quotient Form mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L498-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L498-L501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem GlobalTheory.orthogonalQuotientForm_mk (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (I : Submodule R M) (x y : B.orthogonal I) :
    orthogonalQuotientForm B hB I (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      B x y := by sorry

attribute [defeq] GlobalTheory.orthogonalQuotientForm_mk
