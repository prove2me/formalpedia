-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_of_mulEquiv
-- name    : GroundTheory.Global.index_range_powMonoidHom_of_mulEquiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:13:57.396242+00:00
-- url     : https://prove2.me/theorems/ada16293-70f7-47ac-bd56-ff2efc592101
-- title:
--   Global: index range pow Monoid Hom of mul Equiv
-- statement:
--   The Global construction uses the index range pow Monoid Hom of mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L23-L26

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

theorem GroundTheory.Global.index_range_powMonoidHom_of_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by sorry
