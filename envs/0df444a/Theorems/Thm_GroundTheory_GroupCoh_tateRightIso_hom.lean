-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateRightIso_hom
-- name    : GroundTheory.GroupCoh.tateRightIso_hom
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:06:42.435966+00:00
-- url     : https://prove2.me/theorems/fa42d500-c4c4-4f2c-99c9-79502ce83376
-- title:
--   Group Coh: tate Right Iso hom
-- statement:
--   The Group Coh construction uses the tate Right Iso hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L117-L118

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorLeft_shortExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]

theorem GroundTheory.GroupCoh.tateRightIso_hom (A B : Rep.{u} k G) (r : ℤ) :
    (tateRightIso A B r).hom = tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl := by sorry
