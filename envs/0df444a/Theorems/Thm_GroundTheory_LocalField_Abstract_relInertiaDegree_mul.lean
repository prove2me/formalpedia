-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_relInertiaDegree_mul
-- name    : GroundTheory.LocalField.Abstract.relInertiaDegree_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:12:52.594889+00:00
-- url     : https://prove2.me/theorems/a1ea7644-724c-492c-b035-8ba8c8c0abd6
-- title:
--   Abstract: rel Inertia Degree mul
-- statement:
--   The Abstract construction uses the rel Inertia Degree mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L36-L38

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G]
variable (d : G →* Multiplicative ℤ̂)
variable {d}

theorem GroundTheory.LocalField.Abstract.relInertiaDegree_mul {K L M : Subgroup G} (hML : M ≤ L) (hLK : L ≤ K) :
    relInertiaDegree d L M * relInertiaDegree d K L = relInertiaDegree d K M := by sorry
