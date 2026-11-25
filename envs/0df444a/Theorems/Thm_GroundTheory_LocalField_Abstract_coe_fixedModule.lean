-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_coe_fixedModule
-- name    : GroundTheory.LocalField.Abstract.coe_fixedModule
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:57.216987+00:00
-- url     : https://prove2.me/theorems/2ac60530-1097-4453-860c-05fb841432dd
-- title:
--   Abstract: coe fixed Module
-- statement:
--   The Abstract construction uses the coe fixed Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L25-L29

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

theorem GroundTheory.LocalField.Abstract.coe_fixedModule (H : Subgroup G) :
    (fixedModule A H : Set A) = MulAction.fixedPoints H A := by sorry
