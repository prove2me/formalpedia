-- Prove2me | Theorems.Thm_GroundTheory_Global_map_range_powMonoidHom
-- name    : GroundTheory.Global.map_range_powMonoidHom
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:25.190805+00:00
-- url     : https://prove2.me/theorems/6fb0ed70-f841-4aaf-98ca-d71976a17c3e
-- title:
--   Global: map range pow Monoid Hom
-- statement:
--   The Global construction uses the map range pow Monoid Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L13-L21

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

theorem GroundTheory.Global.map_range_powMonoidHom {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.map (e : G →* H) = (powMonoidHom n : H →* H).range := by sorry
