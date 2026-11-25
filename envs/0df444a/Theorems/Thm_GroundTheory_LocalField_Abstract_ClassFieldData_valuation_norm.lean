-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.valuation_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:03:30.012828+00:00
-- url     : https://prove2.me/theorems/0f59b036-cea3-4df3-a04c-ade465e96fea
-- title:
--   Class Field Data: valuation norm
-- statement:
--   The Class Field Data construction uses the valuation norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L280-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L280-L283

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.valuation_norm {K L : OpenSubgroup G} (hLK : L ≤ K) (a : fixedModule A (L : Subgroup G)) :
    D.valuation K (norm A (K : Subgroup G) (L : Subgroup G) a) = D.valuation L a ^ relInertiaDegree D.deg K L := by sorry
