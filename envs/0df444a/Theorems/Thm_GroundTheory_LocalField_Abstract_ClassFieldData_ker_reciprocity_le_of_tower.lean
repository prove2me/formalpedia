-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_ker_reciprocity_le_of_tower
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.ker_reciprocity_le_of_tower
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:39.070862+00:00
-- url     : https://prove2.me/theorems/1dd861e4-f58b-4e37-b758-3aecd5381395
-- title:
--   Class Field Data: ker reciprocity le of tower
-- statement:
--   The Class Field Data construction uses the ker reciprocity le of tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L189-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L189-L291

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.ker_reciprocity_le_of_tower
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K))
    (hs : Function.Surjective (D.reciprocity hLM hax))
    (hk : (D.reciprocity hLM hax).ker ≤ commutator ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)) :
    (D.reciprocity (hLM.trans hMK) hax).ker ≤
      commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by sorry
