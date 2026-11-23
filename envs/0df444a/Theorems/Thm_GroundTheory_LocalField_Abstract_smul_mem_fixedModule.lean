-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule
-- name    : GroundTheory.LocalField.Abstract.smul_mem_fixedModule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:06.635851+00:00
-- url     : https://prove2.me/theorems/76bbf16b-e137-45f0-9f18-e168fedaebc1
-- title:
--   Abstract: smul mem fixed Module
-- statement:
--   The Abstract construction uses the smul mem fixed Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L31-L35

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

theorem GroundTheory.LocalField.Abstract.smul_mem_fixedModule {H : Subgroup G} {a : A} (ha : a ∈ fixedModule A H) (g : G) :
    g • a ∈ fixedModule A (H.map (MulAut.conj g).toMonoidHom) := by sorry
