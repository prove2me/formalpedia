-- Prove2me | Theorems.Thm_GlobalTheory_orthogonal_orthogonal_of_isTorsionFree_quotient
-- name    : GlobalTheory.orthogonal_orthogonal_of_isTorsionFree_quotient
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:32.890407+00:00
-- url     : https://prove2.me/theorems/6395cdca-e7ea-431e-9158-b1b1ee3bf8e2
-- title:
--   Global Theory: orthogonal orthogonal of is Torsion Free quotient
-- statement:
--   The Global Theory construction uses the orthogonal orthogonal of is Torsion Free quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L544-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L544-L552

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

theorem GlobalTheory.orthogonal_orthogonal_of_isTorsionFree_quotient (hB : B.IsAlt) (hp : Surjective B)
    (hI : IsTorsionFree R (M ⧸ I)) : B.orthogonal (B.orthogonal I) = I := by sorry
