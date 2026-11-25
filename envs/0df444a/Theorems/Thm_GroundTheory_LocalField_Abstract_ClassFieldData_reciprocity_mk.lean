-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_mk
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:41.701794+00:00
-- url     : https://prove2.me/theorems/c16efd18-7302-542d-9a74-6c9e2242fb6a
-- title:
--   Class Field Data: reciprocity mk
-- statement:
--   The Class Field Data construction uses the reciprocity mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ReciprocityMap.lean#L154-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ReciprocityMap.lean#L154-L161

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
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
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
variable (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_mk (s : D.FrobeniusLift K) :
    D.reciprocity hLK hax ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = D.recFrob L hLK s := by sorry
