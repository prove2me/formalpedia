-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_infinitePlaceCompletion
-- name    : GroundTheory.Global.index_range_powMonoidHom_infinitePlaceCompletion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:40.696313+00:00
-- url     : https://prove2.me/theorems/065eef3b-f089-42a7-80cb-ecf093cad55f
-- title:
--   Global: index range pow Monoid Hom infinite Place Completion
-- statement:
--   The Global construction uses the index range pow Monoid Hom infinite Place Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalConditionIndex.lean#L31-L44

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
omit [NumberField K]
open Classical

theorem GroundTheory.Global.index_range_powMonoidHom_infinitePlaceCompletion (w : InfinitePlace K) {n : ℕ}
    (hn : n ≠ 0) :
    (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range.index =
      if w.IsReal ∧ Even n then 2 else 1 := by sorry
