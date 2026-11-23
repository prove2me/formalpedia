-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule_of_normal
-- name    : GroundTheory.LocalField.Abstract.smul_mem_fixedModule_of_normal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:51.529804+00:00
-- url     : https://prove2.me/theorems/e454d25f-6684-4f10-8896-9e985d76bf34
-- title:
--   Abstract: smul mem fixed Module of normal
-- statement:
--   The Abstract construction uses the smul mem fixed Module of normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L99-L106

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
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
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable (K L : Subgroup G)
variable {A K L}

theorem GroundTheory.LocalField.Abstract.smul_mem_fixedModule_of_normal (hLK : L ≤ K) [hN : (L.subgroupOf K).Normal] {g : G}
    (hg : g ∈ K) {a : A} (ha : a ∈ fixedModule A L) : g • a ∈ fixedModule A L := by sorry
