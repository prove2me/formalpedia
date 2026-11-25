-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_smul_smul_neg_self
-- name    : GroundTheory.GroupCoh.smul_smul_neg_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:34.875146+00:00
-- url     : https://prove2.me/theorems/b6db92c7-3286-5cbe-953d-19c47180d2a3
-- title:
--   Group Coh: smul smul neg self
-- statement:
--   The Group Coh construction uses the smul smul neg self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L254-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L254-L255

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
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

theorem GroundTheory.GroupCoh.smul_smul_neg_self {M : ModuleCat.{u} k} (c : k) (x : M) : c • (c • -x) = -(c • (c • x)) := by sorry
