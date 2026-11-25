-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_map_relDeg_iff
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.mem_map_relDeg_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:36.124627+00:00
-- url     : https://prove2.me/theorems/e8b6515c-7d7f-4dff-b2ab-7b19e3e125ff
-- title:
--   Class Field Data: mem map rel Deg iff
-- statement:
--   The Class Field Data construction uses the mem map rel Deg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L202-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L202-L216

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.mem_map_relDeg_iff {K L : OpenSubgroup G} (hLK : L ≤ K) {x : Multiplicative ℤ̂} :
    x ∈ ((L : Subgroup G).subgroupOf K).map (D.relDeg K) ↔
      ∃ y, y ^ relInertiaDegree D.deg K L = x := by sorry
