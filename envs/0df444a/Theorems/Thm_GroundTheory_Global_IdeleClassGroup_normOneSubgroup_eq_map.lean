-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleClassGroup_normOneSubgroup_eq_map
-- name    : GroundTheory.Global.IdeleClassGroup.normOneSubgroup_eq_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:20.037992+00:00
-- url     : https://prove2.me/theorems/c19a7adb-7a50-4121-80ff-9c044042858e
-- title:
--   Idele Class Group: norm One Subgroup eq map
-- statement:
--   The Idele Class Group construction uses the norm One Subgroup eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L243-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L243-L253

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
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
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleClassGroup

theorem GroundTheory.Global.IdeleClassGroup.normOneSubgroup_eq_map :
    normOneSubgroup K = (IdeleGroup.normOneSubgroup K).map (mk K) := by sorry
