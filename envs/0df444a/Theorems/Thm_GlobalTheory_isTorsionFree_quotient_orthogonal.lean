-- Prove2me | Theorems.Thm_GlobalTheory_isTorsionFree_quotient_orthogonal
-- name    : GlobalTheory.isTorsionFree_quotient_orthogonal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:32.6469+00:00
-- url     : https://prove2.me/theorems/4a369d6e-5b04-48cd-8c67-2ab526991c9c
-- title:
--   Global Theory: is Torsion Free quotient orthogonal
-- statement:
--   The Global Theory construction uses the is Torsion Free quotient orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L518-L521
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L518-L521

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

theorem GlobalTheory.isTorsionFree_quotient_orthogonal [IsDomain R] (B : LinearMap.BilinForm R M)
    (I : Submodule R M) : IsTorsionFree R (M ⧸ B.orthogonal I) := by sorry
