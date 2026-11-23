-- Prove2me | Theorems.Thm_GlobalTheory_bijective_neg_bilinForm
-- name    : GlobalTheory.bijective_neg_bilinForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:55.662254+00:00
-- url     : https://prove2.me/theorems/b10e8b22-2bb2-4ed8-a58a-f404a4d33b85
-- title:
--   Global Theory: bijective neg bilin Form
-- statement:
--   The Global Theory construction uses the bijective neg bilin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L407-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L407-L408

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
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}

theorem GlobalTheory.bijective_neg_bilinForm (h : Bijective B) : Bijective (-B) := by sorry
