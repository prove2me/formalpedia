-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_mk_eq_norm
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_mk_eq_norm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:12.687667+00:00
-- url     : https://prove2.me/theorems/1745cf71-0fa8-41a2-9e22-dea39ae20d02
-- title:
--   Class Field Data: reciprocity mk eq norm
-- statement:
--   The Class Field Data construction uses the reciprocity mk eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ReciprocityMap.lean#L163-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ReciprocityMap.lean#L163-L171

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_mk_eq_norm (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK hax ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (QuotientGroup.mk (norm A (K : Subgroup G)
        ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
          tateZero A (K : Subgroup G) (L : Subgroup G)) := by sorry
