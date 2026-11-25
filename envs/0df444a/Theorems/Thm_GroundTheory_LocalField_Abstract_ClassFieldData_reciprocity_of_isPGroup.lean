-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_of_isPGroup
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_of_isPGroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:08.39228+00:00
-- url     : https://prove2.me/theorems/18046947-91c7-50e9-bd15-d6f94943f9e6
-- title:
--   Class Field Data: reciprocity of is PGroup
-- statement:
--   The Class Field Data construction uses the reciprocity of is PGroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L297-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L297-L346

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (n : ℕ) :
    ∀ {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal],
      (L : Subgroup G).relIndex K = n →
      IsPGroup p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) →
      Function.Surjective (D.reciprocity hLK hax) ∧
        (D.reciprocity hLK hax).ker ≤ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by sorry
