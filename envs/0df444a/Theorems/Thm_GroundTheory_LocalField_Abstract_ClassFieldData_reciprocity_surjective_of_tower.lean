-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_surjective_of_tower
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_surjective_of_tower
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:13.024238+00:00
-- url     : https://prove2.me/theorems/ff552db4-eae9-5612-84a0-6a22f83f95e4
-- title:
--   Class Field Data: reciprocity surjective of tower
-- statement:
--   The Class Field Data construction uses the reciprocity surjective of tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L168-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L168-L187

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
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
variable {K M L : OpenSubgroup G} (hLM : L ≤ M) (hMK : M ≤ K)
  [((L : Subgroup G).subgroupOf K).Normal] [((L : Subgroup G).subgroupOf M).Normal]
  [((M : Subgroup G).subgroupOf K).Normal]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_surjective_of_tower (h1 : Function.Surjective (D.reciprocity hLM hax))
    (h2 : Function.Surjective (D.reciprocity hMK hax)) :
    Function.Surjective (D.reciprocity (hLM.trans hMK) hax) := by sorry
