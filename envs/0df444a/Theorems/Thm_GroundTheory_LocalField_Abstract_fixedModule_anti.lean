-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
-- name    : GroundTheory.LocalField.Abstract.fixedModule_anti
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:01.039911+00:00
-- url     : https://prove2.me/theorems/66a1d268-7cd2-477e-a7f6-8a2c944c3141
-- title:
--   Abstract: fixed Module anti
-- statement:
--   The Abstract construction uses the fixed Module anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L22-L23

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

theorem GroundTheory.LocalField.Abstract.fixedModule_anti {H H' : Subgroup G} (h : H ≤ H') : fixedModule A H' ≤ fixedModule A H := by sorry
