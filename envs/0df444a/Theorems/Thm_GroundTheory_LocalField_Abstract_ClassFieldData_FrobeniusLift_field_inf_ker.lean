-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_inf_ker
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift.field_inf_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:28:43.01814+00:00
-- url     : https://prove2.me/theorems/0ba9418a-6764-465d-baca-906029465704
-- title:
--   Frobenius Lift: field inf ker
-- statement:
--   The Frobenius Lift construction uses the field inf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Reciprocity.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Reciprocity.lean#L77-L80

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
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
  (D : ClassFieldData G A)
variable {D} {K L : OpenSubgroup G}
open GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift.field_inf_ker :
    ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker = (L : Subgroup G) ⊓ D.deg.ker := by sorry
