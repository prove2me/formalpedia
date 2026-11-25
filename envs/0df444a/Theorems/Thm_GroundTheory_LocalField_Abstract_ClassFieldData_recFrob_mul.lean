-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_recFrob_mul
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.recFrob_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:35:17.148813+00:00
-- url     : https://prove2.me/theorems/29b456f0-c6d6-4782-979b-d4cc73330f07
-- title:
--   Class Field Data: rec Frob mul
-- statement:
--   The Class Field Data construction uses the rec Frob mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L323-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L323-L356

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.recFrob_mul (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (s t : D.FrobeniusLift K) :
    D.recFrob L hLK (s.mul t) = D.recFrob L hLK s * D.recFrob L hLK t := by sorry
