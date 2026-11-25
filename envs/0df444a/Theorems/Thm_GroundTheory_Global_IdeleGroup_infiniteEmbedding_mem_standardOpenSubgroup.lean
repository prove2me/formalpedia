-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteEmbedding_mem_standardOpenSubgroup
-- name    : GroundTheory.Global.IdeleGroup.infiniteEmbedding_mem_standardOpenSubgroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:19:11.335806+00:00
-- url     : https://prove2.me/theorems/bfc0aa11-cb58-43a5-86a3-8387b1ff4425
-- title:
--   Idele Group: infinite Embedding mem standard Open Subgroup
-- statement:
--   The Idele Group construction uses the infinite Embedding mem standard Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L58-L64

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup

theorem GroundTheory.Global.IdeleGroup.infiniteEmbedding_mem_standardOpenSubgroup (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infiniteEmbedding w x ∈ standardOpenSubgroup K := by sorry
