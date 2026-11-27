-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_augmentation_le_map_ker
-- name    : GroundTheory.LocalField.Abstract.augmentation_le_map_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:39.538571+00:00
-- url     : https://prove2.me/theorems/5c197da9-d6b0-5463-8c2a-479b0395e3c1
-- title:
--   Abstract: augmentation le map ker
-- statement:
--   The Abstract construction uses the augmentation le map ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L169-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L169-L176

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
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
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable (K L : Subgroup G)
variable {A K L}
variable (A K L)
variable [(L.subgroupOf K).FiniteIndex]
variable {A K L}
variable (A K L)
variable {A K L}

theorem GroundTheory.LocalField.Abstract.augmentation_le_map_ker (hLK : L ≤ K) [(L.subgroupOf K).Normal] :
    augmentation A K L ≤ (norm A K L).ker.map (fixedModule A L).subtype := by sorry
