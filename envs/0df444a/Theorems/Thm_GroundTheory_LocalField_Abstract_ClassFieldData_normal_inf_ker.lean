-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_normal_inf_ker
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.normal_inf_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:35:26.208067+00:00
-- url     : https://prove2.me/theorems/4fd7a573-e08e-4e67-98f1-b94dbbd7f55b
-- title:
--   Class Field Data: normal inf ker
-- statement:
--   The Class Field Data construction uses the normal inf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L130-L135

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
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
omit [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.normal_inf_ker (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((L : Subgroup G) ⊓ D.deg.ker).subgroupOf ((K : Subgroup G) ⊓ D.deg.ker)).Normal := by sorry
