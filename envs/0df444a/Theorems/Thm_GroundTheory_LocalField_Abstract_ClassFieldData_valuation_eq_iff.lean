-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_eq_iff
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.valuation_eq_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:03:14.809234+00:00
-- url     : https://prove2.me/theorems/9c733ce0-f434-4f9f-afe7-07d49ed431df
-- title:
--   Class Field Data: valuation eq iff
-- statement:
--   The Class Field Data construction uses the valuation eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L257-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L257-L259

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
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
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)

theorem GroundTheory.LocalField.Abstract.ClassFieldData.valuation_eq_iff (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) (z : Multiplicative ℤ̂) :
    D.valuation K a = z ↔ D.val (norm A ⊤ (K : Subgroup G) a) = z ^ inertiaDegree D.deg K := by sorry
