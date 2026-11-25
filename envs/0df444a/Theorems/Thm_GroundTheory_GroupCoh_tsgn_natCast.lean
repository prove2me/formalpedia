-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tsgn_natCast
-- name    : GroundTheory.GroupCoh.tsgn_natCast
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:51:56.078169+00:00
-- url     : https://prove2.me/theorems/8050b3ba-aa1f-46cb-8d70-6af632344100
-- title:
--   Group Coh: tsgn nat Cast
-- statement:
--   The Group Coh construction uses the tsgn nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L56-L59

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

theorem GroundTheory.GroupCoh.tsgn_natCast (n : ℕ) : tsgn k n = (-1 : k) ^ n := by sorry
