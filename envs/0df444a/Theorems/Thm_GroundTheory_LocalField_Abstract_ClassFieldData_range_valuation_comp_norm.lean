-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_range_valuation_comp_norm
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.range_valuation_comp_norm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:42.239319+00:00
-- url     : https://prove2.me/theorems/6f84e0f2-6e8c-5876-96ca-a8ebd856ccf5
-- title:
--   Class Field Data: range valuation comp norm
-- statement:
--   The Class Field Data construction uses the range valuation comp norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L285-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L285-L297

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.range_valuation_comp_norm {K L : OpenSubgroup G} (hLK : L ≤ K) :
    ((D.valuation K).comp (norm A (K : Subgroup G) (L : Subgroup G))).range =
      (D.valuation K).range.map (powMonoidHom (relInertiaDegree D.deg K L)) := by sorry
