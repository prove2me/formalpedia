-- Prove2me | Theorems.Thm_GroundTheory_Global_index_map_mul_relIndex_ker
-- name    : GroundTheory.Global.index_map_mul_relIndex_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:12:59.410882+00:00
-- url     : https://prove2.me/theorems/6ca85ff7-4458-4997-a398-d9260ece10a6
-- title:
--   Global: index map mul rel Index ker
-- statement:
--   The Global construction uses the index map mul rel Index ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexFormula.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexFormula.lean#L12-L15

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexFormula
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
variable {G C : Type*} [Group G] [Group C]

theorem GroundTheory.Global.index_map_mul_relIndex_ker {f : G →* C} (hf : Function.Surjective f) (W : Subgroup G)
    [W.Normal] : (W.map f).index * W.relIndex f.ker = W.index := by sorry
