-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_norm_mem_range_of_mem_units
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.norm_mem_range_of_mem_units
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:17.635835+00:00
-- url     : https://prove2.me/theorems/de61749e-2bc8-491b-8095-69344cd0918f
-- title:
--   Class Field Data: norm mem range of mem units
-- statement:
--   The Class Field Data construction uses the norm mem range of mem units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Reciprocity.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Reciprocity.lean#L121-L133

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
omit [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.norm_mem_range_of_mem_units (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {u : fixedModule A (S : Subgroup G)}
    (hu' : u ∈ D.units S) :
    norm A (K : Subgroup G) (S : Subgroup G) u ∈ (norm A (K : Subgroup G) (L : Subgroup G)).range := by sorry
