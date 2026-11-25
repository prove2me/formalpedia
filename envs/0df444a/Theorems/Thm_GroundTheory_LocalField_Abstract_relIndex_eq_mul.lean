-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_relIndex_eq_mul
-- name    : GroundTheory.LocalField.Abstract.relIndex_eq_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:03:18.127921+00:00
-- url     : https://prove2.me/theorems/abb84b13-e487-4eb6-bc16-832d31da60fa
-- title:
--   Abstract: rel Index eq mul
-- statement:
--   The Abstract construction uses the rel Index eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L57-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L57-L90

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

theorem GroundTheory.LocalField.Abstract.relIndex_eq_mul {K L : Subgroup G} (hLK : L ≤ K) :
    L.relIndex K = relRamificationIndex d K L * relInertiaDegree d K L := by sorry
