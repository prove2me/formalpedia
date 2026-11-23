-- Prove2me | Theorems.Thm_GlobalTheory_exists_pair_dvd_of_bilinForm
-- name    : GlobalTheory.exists_pair_dvd_of_bilinForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:55.916923+00:00
-- url     : https://prove2.me/theorems/00d46c4c-107b-4320-8bb7-96302d892ebe
-- title:
--   Global Theory: exists pair dvd of bilin Form
-- statement:
--   The Global Theory construction uses the exists pair dvd of bilin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L135-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean#L135-L161

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
  [Module R M]
omit [IsDomain R]

theorem GlobalTheory.exists_pair_dvd_of_bilinForm (B : LinearMap.BilinForm R M) (N : Submodule R M) :
    ∃ e ∈ N, ∃ f ∈ N, (∀ y ∈ N, B e f ∣ B e y) ∧ (∀ x ∈ N, B e f ∣ B x f) ∧
      (∀ x ∈ N, ∀ y ∈ N, B e y = 0 → B x f = 0 → B e f ∣ B x y) := by sorry
