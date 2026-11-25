-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_frobeniusLift_mk
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.exists_frobeniusLift_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:48.692939+00:00
-- url     : https://prove2.me/theorems/7181e6ea-6db3-4649-a6d8-1f3d5645e8e3
-- title:
--   Class Field Data: exists frobenius Lift mk
-- statement:
--   The Class Field Data construction uses the exists frobenius Lift mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ReciprocityMap.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ReciprocityMap.lean#L176-L180

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
include hLK
omit [IsDiscreteModule G A] [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.exists_frobeniusLift_mk (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    ∃ s : D.FrobeniusLift K,
      ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = q := by sorry
