-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorLeft_shortExact
-- name    : GroundTheory.GroupCoh.augSES_tensorLeft_shortExact
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:50.073034+00:00
-- url     : https://prove2.me/theorems/c9dcc38a-1e2a-4385-be28-14ded4b8bce8
-- title:
--   Group Coh: aug SES tensor Left short Exact
-- statement:
--   The Group Coh construction uses the aug SES tensor Left short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L338-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L338-L341

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}

theorem GroundTheory.GroupCoh.augSES_tensorLeft_shortExact (A B : Rep.{u} k G) :
    (((augSES k G).obj B).map (tensorLeft A)).ShortExact := by sorry
