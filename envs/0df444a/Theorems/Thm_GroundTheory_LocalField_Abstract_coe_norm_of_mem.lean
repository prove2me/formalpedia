-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_of_mem
-- name    : GroundTheory.LocalField.Abstract.coe_norm_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:03.384321+00:00
-- url     : https://prove2.me/theorems/ae9af37d-59fc-4779-8b57-af6651075e47
-- title:
--   Abstract: coe norm of mem
-- statement:
--   The Abstract construction uses the coe norm of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L35-L46

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
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
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
variable {K L : Subgroup G} [(L.subgroupOf K).FiniteIndex]

theorem GroundTheory.LocalField.Abstract.coe_norm_of_mem (hLK : L ≤ K) {a : A} (ha : a ∈ fixedModule A K) :
    (norm A K L ⟨a, fixedModule_anti hLK ha⟩ : A) = a ^ L.relIndex K := by sorry
