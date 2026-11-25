-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_relIndex_sup_of_le_normalizer
-- name    : GroundTheory.LocalField.Abstract.relIndex_sup_of_le_normalizer
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:03:11.019295+00:00
-- url     : https://prove2.me/theorems/0f2a5f35-6a62-4587-81a2-89c9b3664917
-- title:
--   Abstract: rel Index sup of le normalizer
-- statement:
--   The Abstract construction uses the rel Index sup of le normalizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L13-L15

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_P2M_GroundTheory_Variant__N1_relIndex_sup_of_le_normalizer_7514b13ff881

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

theorem GroundTheory.LocalField.Abstract.relIndex_sup_of_le_normalizer {H N : Subgroup G} (hLE : H ≤ Subgroup.normalizer (N : Set G)) :
    H.relIndex (H ⊔ N) = H.relIndex N := by sorry
