-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_inertiaDegree_relDeg
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.inertiaDegree_relDeg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:48.35759+00:00
-- url     : https://prove2.me/theorems/da8719d5-0774-4409-9f8c-4614bab6ceb7
-- title:
--   Class Field Data: inertia Degree rel Deg
-- statement:
--   The Class Field Data construction uses the inertia Degree rel Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L218-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L218-L227

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.inertiaDegree_relDeg {K L : OpenSubgroup G} (hLK : L ≤ K) :
    inertiaDegree (D.relDeg K) ((L : Subgroup G).subgroupOf K) = relInertiaDegree D.deg K L := by sorry
