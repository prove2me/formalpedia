-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_shiftSC_shortExact
-- name    : GroundTheory.GroupCoh.shiftSC_shortExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:08.009815+00:00
-- url     : https://prove2.me/theorems/9707c261-058d-4925-8884-ed85f5cddc4f
-- title:
--   Group Coh: shift SC short Exact
-- statement:
--   The Group Coh construction uses the shift SC short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L73-L76

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]

theorem GroundTheory.GroupCoh.shiftSC_shortExact : (shiftSC A).ShortExact := by sorry
