-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_field_le_field_of_pow
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.field_le_field_of_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:45:24.246277+00:00
-- url     : https://prove2.me/theorems/82f6ca0d-075b-40ca-9a97-eca69898c9cc
-- title:
--   Class Field Data: field le field of pow
-- statement:
--   The Class Field Data construction uses the field le field of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L149-L154

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
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.field_le_field_of_pow (s1 s2 : D.FrobeniusLift K) (k : ℕ) (h2 : s2.elt = s1.elt ^ k) :
    s2.field L hLK ≤ s1.field L hLK := by sorry
