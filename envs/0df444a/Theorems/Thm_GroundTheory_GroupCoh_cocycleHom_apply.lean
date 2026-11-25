-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_cocycleHom_apply
-- name    : GroundTheory.GroupCoh.cocycleHom_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:12.549722+00:00
-- url     : https://prove2.me/theorems/41d857ec-2572-54b0-b561-3dbbc2515fe1
-- title:
--   Group Coh: cocycle Hom apply
-- statement:
--   The Group Coh construction uses the cocycle Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugTrivial.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugTrivial.lean#L90-L91

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
variable {A : Rep.{u} k G}

theorem GroundTheory.GroupCoh.cocycleHom_apply (f : cocycles₁ A) (x : augIdeal k G) :
    (cocycleHom f).hom x = cocycleLinear f x.1 := by sorry
