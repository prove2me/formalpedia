-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_galRestrict_surjective
-- name    : GroundTheory.LocalField.Abstract.galRestrict_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:31.813815+00:00
-- url     : https://prove2.me/theorems/bff3488a-49d5-5b19-8c8d-0a94a57ef3d3
-- title:
--   Abstract: gal Restrict surjective
-- statement:
--   The Abstract construction uses the gal Restrict surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L110-L115

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoPGroup
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
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
omit [IsTopologicalGroup G] [CompactSpace G]

theorem GroundTheory.LocalField.Abstract.galRestrict_surjective {K L M : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((M : Subgroup G).subgroupOf K).Normal] (hLM : L ≤ M) :
    Function.Surjective (galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM) := by sorry
