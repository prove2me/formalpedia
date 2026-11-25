-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_augCocycle_apply
-- name    : GroundTheory.GroupCoh.augCocycle_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:00:53.538434+00:00
-- url     : https://prove2.me/theorems/de412121-e6ef-40c2-82da-aedca8c4c1e7
-- title:
--   Group Coh: aug Cocycle apply
-- statement:
--   The Group Coh construction uses the aug Cocycle apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugTrivial.lean#L114-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugTrivial.lean#L114-L114

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable (k G : Type u) [CommRing k] [Group G]
variable {k G}
variable (k) {H : Type u} [Group H] (φ : H →* G)

theorem GroundTheory.GroupCoh.augCocycle_apply (h : H) : augCocycle k φ h = augIdealSubOne (φ h) := by sorry

attribute [defeq] GroundTheory.GroupCoh.augCocycle_apply
