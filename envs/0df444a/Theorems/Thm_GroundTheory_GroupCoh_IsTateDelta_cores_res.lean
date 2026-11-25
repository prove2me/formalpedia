-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_IsTateDelta_cores_res
-- name    : GroundTheory.GroupCoh.IsTateDelta.cores_res
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:03.249752+00:00
-- url     : https://prove2.me/theorems/b70234fc-317b-454a-b3cf-4a1dc73b78a7
-- title:
--   Is Tate Delta: cores res
-- statement:
--   The Is Tate Delta construction uses the cores res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L96-L98

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
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
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
open GroundTheory.GroupCoh.IsTateDelta
variable {U V W : Subgroup G} [Fintype U] [Fintype V] [Fintype W]

theorem GroundTheory.GroupCoh.IsTateDelta.cores_res : IsTateDelta (fun n => tateCores (k := k) U n ≫ tateRes V n) := by sorry
