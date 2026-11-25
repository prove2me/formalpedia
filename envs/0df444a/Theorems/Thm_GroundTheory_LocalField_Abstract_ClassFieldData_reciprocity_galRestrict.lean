-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_galRestrict
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_galRestrict
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:16.920483+00:00
-- url     : https://prove2.me/theorems/42cfa4e1-2a8b-4c4f-b601-1c0ace3a46a4
-- title:
--   Class Field Data: reciprocity gal Restrict
-- statement:
--   The Class Field Data construction uses the reciprocity gal Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L226-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L226-L259

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
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
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] {D : ClassFieldData G A}
variable [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_galRestrict (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {K L K' L' : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (hL'K' : L' ≤ K') [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (q : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') :
    D.reciprocity hLK hax (galRestrict hK hL q) =
      normTateZero hK hL hL'K' hLK (D.reciprocity hL'K' hax q) := by sorry
