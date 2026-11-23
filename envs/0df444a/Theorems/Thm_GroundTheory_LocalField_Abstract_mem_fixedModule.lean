-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_mem_fixedModule
-- name    : GroundTheory.LocalField.Abstract.mem_fixedModule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:05.611429+00:00
-- url     : https://prove2.me/theorems/1b4f60ab-a969-4073-a07e-2a4f4d3b990a
-- title:
--   Abstract: mem fixed Module
-- statement:
--   The Abstract construction uses the mem fixed Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L18-L20

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
variable {A}

theorem GroundTheory.LocalField.Abstract.mem_fixedModule {H : Subgroup G} {a : A} :
    a ∈ fixedModule A H ↔ ∀ g ∈ H, g • a = a := by sorry
