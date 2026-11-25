-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_of_mem
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.valuation_of_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:03:46.641859+00:00
-- url     : https://prove2.me/theorems/d130f456-d84a-4a37-bea0-cebbfd04a238
-- title:
--   Class Field Data: valuation of mem
-- statement:
--   The Class Field Data construction uses the valuation of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L299-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L299-L307

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.valuation_of_mem {K L : OpenSubgroup G} (hLK : L ≤ K) {a : A} (ha : a ∈ fixedModule A (K : Subgroup G)) :
    D.valuation L ⟨a, fixedModule_anti hLK ha⟩ =
      D.valuation K ⟨a, ha⟩ ^ relRamificationIndex D.deg K L := by sorry
