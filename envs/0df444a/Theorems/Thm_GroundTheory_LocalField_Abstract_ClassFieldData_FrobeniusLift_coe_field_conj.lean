-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_coe_field_conj
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift.coe_field_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:00.533622+00:00
-- url     : https://prove2.me/theorems/f56feaa6-cf93-53fd-9983-15c50a072b7e
-- title:
--   Frobenius Lift: coe field conj
-- statement:
--   The Frobenius Lift construction uses the coe field conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L274-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L274-L278

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift.coe_field_conj (ρ : G) {K L : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K) :
    (((s.conj ρ).field (conjOpen ρ L) (conjOpen_mono ρ hLK) : OpenSubgroup G) : Subgroup G) =
      ((s.field L hLK : OpenSubgroup G) : Subgroup G).map (MulAut.conj ρ).toMonoidHom := by sorry
