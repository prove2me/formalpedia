-- Prove2me | Theorems.Thm_GlobalTheory_dualRestrict_surjective_of_isTorsionFree_quotient
-- name    : GlobalTheory.dualRestrict_surjective_of_isTorsionFree_quotient
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:19.448273+00:00
-- url     : https://prove2.me/theorems/e32568a0-dcf0-48d4-a83a-e32c7f6adb25
-- title:
--   Global Theory: dual Restrict surjective of is Torsion Free quotient
-- statement:
--   The Global Theory construction uses the dual Restrict surjective of is Torsion Free quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L539-L542
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L539-L542

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
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] {B : LinearMap.BilinForm R M} {I : Submodule R M}

theorem GlobalTheory.dualRestrict_surjective_of_isTorsionFree_quotient (hI : IsTorsionFree R (M ⧸ I)) :
    Surjective I.dualRestrict := by sorry
